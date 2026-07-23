Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition MeasAndMobParametersCommon__supportedGapPattern__Type := bit_string_fixed.
Definition MeasAndMobParametersCommon__supportedGapPattern__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 22 /\ bit_string_len_prop (fst z) (snd z)).
Inductive MeasAndMobParametersCommon__ssb_RLM__Type : Set :=
 | MeasAndMobParametersCommon__ssb_RLM__supported
.
Definition MeasAndMobParametersCommon__ssb_RLM__cond := (fun (_ : MeasAndMobParametersCommon__ssb_RLM__Type) => True).
Lemma MeasAndMobParametersCommon__ssb_RLM__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ssb_RLM__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ssb_RLM__nat__helper.

Definition MeasAndMobParametersCommon__ssb_RLM__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ssb_RLM__supported => 0
  end.
Definition MeasAndMobParametersCommon__ssb_RLM__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ssb_RLM__supported
  | _ => MeasAndMobParametersCommon__ssb_RLM__supported
  end.
Lemma MeasAndMobParametersCommon__ssb_RLM__F1F2 : forall x : MeasAndMobParametersCommon__ssb_RLM__Type, (MeasAndMobParametersCommon__ssb_RLM__F1 x <= 0) /\ MeasAndMobParametersCommon__ssb_RLM__F2 (MeasAndMobParametersCommon__ssb_RLM__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ssb_RLM__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ssb_RLM__F1 (MeasAndMobParametersCommon__ssb_RLM__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Type : Set :=
 | MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__supported
.
Definition MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__cond := (fun (_ : MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Type) => True).
Lemma MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__nat__helper.

Definition MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__supported => 0
  end.
Definition MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__supported
  | _ => MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__supported
  end.
Lemma MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F1F2 : forall x : MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Type, (MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F1 x <= 0) /\ MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F2 (MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F1 (MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Type : Set :=
 | MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__supported
.
Definition MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__cond := (fun (_ : MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Type) => True).
Lemma MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__nat__helper.

Definition MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__supported
  | _ => MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__supported
  end.
Lemma MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F1F2 : forall x : MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Type, (MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F1 x <= 0) /\ MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F2 (MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F1 (MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Type : Set :=
 | MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__supported
.
Definition MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__cond := (fun (_ : MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Type) => True).
Lemma MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__nat__helper.

Definition MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__supported
  | _ => MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__supported
  end.
Lemma MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F1F2 : forall x : MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Type, (MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F1 x <= 0) /\ MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F2 (MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F1 (MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Type : Set :=
 | MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__supported
.
Definition MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__cond := (fun (_ : MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Type) => True).
Lemma MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__nat__helper.

Definition MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__supported
  | _ => MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__supported
  end.
Lemma MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F1F2 : forall x : MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Type, (MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F1 x <= 0) /\ MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F2 (MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F1 (MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Type : Set :=
 | MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__supported
.
Definition MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__cond := (fun (_ : MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Type) => True).
Lemma MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__nat__helper.

Definition MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__supported
  | _ => MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__supported
  end.
Lemma MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F1F2 : forall x : MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Type, (MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F1 x <= 0) /\ MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F2 (MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F1 (MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersCommon__ext0O__Type : Set :=
  make__MeasAndMobParametersCommon__ext0O__Type {
    MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport : option MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Type ;
    MeasAndMobParametersCommon__ext0O__handoverFDD_TDD : option MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Type ;
    MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting : option MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Type ;
    MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting : option MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Type ;
}.
Definition MeasAndMobParametersCommon__ext0O__list := (
 Opt MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Type MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__cond ::
 Opt MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Type MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__cond ::
 Opt MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Type MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__cond ::
 Opt MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Type MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext0O__cond z := 
  opt_cond MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__cond (MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport z) /\
  opt_cond MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__cond (MeasAndMobParametersCommon__ext0O__handoverFDD_TDD z) /\
  opt_cond MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__cond (MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting z) /\
  opt_cond MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__cond (MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting z) /\
  True.

Definition MeasAndMobParametersCommon__ext0__Type := MeasAndMobParametersCommon__ext0O__Type.
Definition MeasAndMobParametersCommon__ext0__cond := MeasAndMobParametersCommon__ext0O__cond.

Inductive MeasAndMobParametersCommon__ext1O__independentGapConfig__Type : Set :=
 | MeasAndMobParametersCommon__ext1O__independentGapConfig__supported
.
Definition MeasAndMobParametersCommon__ext1O__independentGapConfig__cond := (fun (_ : MeasAndMobParametersCommon__ext1O__independentGapConfig__Type) => True).
Lemma MeasAndMobParametersCommon__ext1O__independentGapConfig__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext1O__independentGapConfig__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext1O__independentGapConfig__nat__helper.

Definition MeasAndMobParametersCommon__ext1O__independentGapConfig__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext1O__independentGapConfig__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext1O__independentGapConfig__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext1O__independentGapConfig__supported
  | _ => MeasAndMobParametersCommon__ext1O__independentGapConfig__supported
  end.
Lemma MeasAndMobParametersCommon__ext1O__independentGapConfig__F1F2 : forall x : MeasAndMobParametersCommon__ext1O__independentGapConfig__Type, (MeasAndMobParametersCommon__ext1O__independentGapConfig__F1 x <= 0) /\ MeasAndMobParametersCommon__ext1O__independentGapConfig__F2 (MeasAndMobParametersCommon__ext1O__independentGapConfig__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext1O__independentGapConfig__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext1O__independentGapConfig__F1 (MeasAndMobParametersCommon__ext1O__independentGapConfig__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Type : Set :=
 | MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__supported
.
Definition MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__cond := (fun (_ : MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Type) => True).
Lemma MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__nat__helper.

Definition MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__supported
  | _ => MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__supported
  end.
Lemma MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F1F2 : forall x : MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Type, (MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F1 x <= 0) /\ MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F2 (MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F1 (MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Type : Set :=
 | MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__supported
.
Definition MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__cond := (fun (_ : MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Type) => True).
Lemma MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__nat__helper.

Definition MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__supported
  | _ => MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__supported
  end.
Lemma MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F1F2 : forall x : MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Type, (MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F1 x <= 0) /\ MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F2 (MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F1 (MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Type : Set :=
 | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n4
 | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n8
 | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n16
 | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n32
 | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n64
 | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n96
.
Definition MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__cond := (fun (_ : MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Type) => True).
Lemma MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__nat__helper.

Definition MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n4 => 0
  | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n8 => 1
  | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n16 => 2
  | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n32 => 3
  | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n64 => 4
  | MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n96 => 5
  end.
Definition MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n4
  | 1 => MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n8
  | 2 => MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n16
  | 3 => MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n32
  | 4 => MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n64
  | 5 => MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n96
  | _ => MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__n4
  end.
Lemma MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F1F2 : forall x : MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Type, (MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F1 x <= 5) /\ MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F2 (MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F2F1 : forall (y : nat) (H : y <= 5), MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F1 (MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersCommon__ext1O__Type : Set :=
  make__MeasAndMobParametersCommon__ext1O__Type {
    MeasAndMobParametersCommon__ext1O__independentGapConfig : option MeasAndMobParametersCommon__ext1O__independentGapConfig__Type ;
    MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport : option MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Type ;
    MeasAndMobParametersCommon__ext1O__handoverFR1_FR2 : option MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Type ;
    MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR : option MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Type ;
}.
Definition MeasAndMobParametersCommon__ext1O__list := (
 Opt MeasAndMobParametersCommon__ext1O__independentGapConfig__Type MeasAndMobParametersCommon__ext1O__independentGapConfig__cond ::
 Opt MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Type MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__cond ::
 Opt MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Type MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__cond ::
 Opt MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Type MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext1O__cond z := 
  opt_cond MeasAndMobParametersCommon__ext1O__independentGapConfig__cond (MeasAndMobParametersCommon__ext1O__independentGapConfig z) /\
  opt_cond MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__cond (MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport z) /\
  opt_cond MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__cond (MeasAndMobParametersCommon__ext1O__handoverFR1_FR2 z) /\
  opt_cond MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__cond (MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR z) /\
  True.

Definition MeasAndMobParametersCommon__ext1__Type := MeasAndMobParametersCommon__ext1O__Type.
Definition MeasAndMobParametersCommon__ext1__cond := MeasAndMobParametersCommon__ext1O__cond.

Inductive MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Type : Set :=
 | MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__supported
.
Definition MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__cond := (fun (_ : MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Type) => True).
Lemma MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__nat__helper.

Definition MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__supported
  | _ => MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__supported
  end.
Lemma MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F1F2 : forall x : MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Type, (MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F1 x <= 0) /\ MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F2 (MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F1 (MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersCommon__ext2O__Type : Set :=
  make__MeasAndMobParametersCommon__ext2O__Type {
    MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC : option MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Type ;
}.
Definition MeasAndMobParametersCommon__ext2O__list := (
 Opt MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Type MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext2O__cond z := 
  opt_cond MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__cond (MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC z) /\
  True.

Definition MeasAndMobParametersCommon__ext2__Type := MeasAndMobParametersCommon__ext2O__Type.
Definition MeasAndMobParametersCommon__ext2__cond := MeasAndMobParametersCommon__ext2O__cond.

Inductive MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Type : Set :=
 | MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__supported
.
Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__cond := (fun (_ : MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Type) => True).
Lemma MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__nat__helper.

Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__supported
  | _ => MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__supported
  end.
Lemma MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F1F2 : forall x : MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Type, (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F1 x <= 0) /\ MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F2 (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F1 (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Type : Set :=
 | MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__supported
.
Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__cond := (fun (_ : MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Type) => True).
Lemma MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__nat__helper.

Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__supported
  | _ => MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__supported
  end.
Lemma MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F1F2 : forall x : MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Type, (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F1 x <= 0) /\ MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F2 (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F1 (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Type : Set :=
 | MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__supported
.
Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__cond := (fun (_ : MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Type) => True).
Lemma MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__nat__helper.

Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__supported
  | _ => MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__supported
  end.
Lemma MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F1F2 : forall x : MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Type, (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F1 x <= 0) /\ MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F2 (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F1 (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Type : Set :=
 | MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__supported
.
Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__cond := (fun (_ : MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Type) => True).
Lemma MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__nat__helper.

Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__supported
  | _ => MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__supported
  end.
Lemma MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F1F2 : forall x : MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Type, (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F1 x <= 0) /\ MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F2 (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F1 (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersCommon__ext3O__Type : Set :=
  make__MeasAndMobParametersCommon__ext3O__Type {
    MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC : option MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Type ;
    MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC : option MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Type ;
    MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC : option MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Type ;
    MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC : option MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Type ;
}.
Definition MeasAndMobParametersCommon__ext3O__list := (
 Opt MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Type MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__cond ::
 Opt MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Type MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__cond ::
 Opt MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Type MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__cond ::
 Opt MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Type MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext3O__cond z := 
  opt_cond MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__cond (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC z) /\
  opt_cond MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__cond (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC z) /\
  opt_cond MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__cond (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC z) /\
  opt_cond MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__cond (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC z) /\
  True.

Definition MeasAndMobParametersCommon__ext3__Type := MeasAndMobParametersCommon__ext3O__Type.
Definition MeasAndMobParametersCommon__ext3__cond := MeasAndMobParametersCommon__ext3O__cond.

Inductive MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Type, (MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F2 (MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F1 (MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Type, (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F2 (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F1 (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Type, (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F2 (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F1 (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Type : Set :=
  make__MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Type {
    MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16 : option MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Type ;
    MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16 : option MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Type ;
}.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list := (
 Opt MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Type MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Type MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond z := 
  opt_cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__cond (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__cond (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16 z) /\
  True.

Inductive MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Type, (MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F2 (MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F1 (MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F2 y) = y. enum_solve H y. Qed.

Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__Type := bit_string_fixed.
Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Inductive MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Type, (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F2 (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F1 (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n8
 | MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n16
 | MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n32
 | MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n64
.
Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n8 => 0
  | MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n16 => 1
  | MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n32 => 2
  | MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n64 => 3
  end.
Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n8
  | 1 => MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n16
  | 2 => MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n32
  | 3 => MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n64
  | _ => MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__n8
  end.
Lemma MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Type, (MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F1 x <= 3) /\ MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F2 (MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F2F1 : forall (y : nat) (H : y <= 3), MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F1 (MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n4
 | MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n8
 | MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n16
 | MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n32
.
Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n4 => 0
  | MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n8 => 1
  | MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n16 => 2
  | MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n32 => 3
  end.
Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n4
  | 1 => MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n8
  | 2 => MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n16
  | 3 => MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n32
  | _ => MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__n4
  end.
Lemma MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Type, (MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F1 x <= 3) /\ MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F2 (MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F2F1 : forall (y : nat) (H : y <= 3), MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F1 (MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n2
 | MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n4
 | MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n8
.
Definition MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n2 => 0
  | MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n4 => 1
  | MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n8 => 2
  end.
Definition MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n2
  | 1 => MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n4
  | 2 => MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n8
  | _ => MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__n2
  end.
Lemma MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Type, (MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F1 x <= 2) /\ MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F2 (MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F2F1 : forall (y : nat) (H : y <= 2), MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F1 (MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Type, (MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F2 (MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F1 (MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__dummy__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__dummy__supported
.
Definition MeasAndMobParametersCommon__ext4O__dummy__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__dummy__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__dummy__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__dummy__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__dummy__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__dummy__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__dummy__supported
  | _ => MeasAndMobParametersCommon__ext4O__dummy__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__dummy__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__dummy__Type, (MeasAndMobParametersCommon__ext4O__dummy__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__dummy__F2 (MeasAndMobParametersCommon__ext4O__dummy__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__dummy__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__dummy__F1 (MeasAndMobParametersCommon__ext4O__dummy__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Type, (MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F2 (MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F1 (MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Type, (MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F2 (MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F1 (MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Type, (MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F2 (MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F1 (MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Type, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F2 (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F1 (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Type, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F2 (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F1 (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Type, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F2 (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F1 (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext4O__pcellT312_r16__Type : Set :=
 | MeasAndMobParametersCommon__ext4O__pcellT312_r16__supported
.
Definition MeasAndMobParametersCommon__ext4O__pcellT312_r16__cond := (fun (_ : MeasAndMobParametersCommon__ext4O__pcellT312_r16__Type) => True).
Lemma MeasAndMobParametersCommon__ext4O__pcellT312_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext4O__pcellT312_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext4O__pcellT312_r16__nat__helper.

Definition MeasAndMobParametersCommon__ext4O__pcellT312_r16__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext4O__pcellT312_r16__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext4O__pcellT312_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext4O__pcellT312_r16__supported
  | _ => MeasAndMobParametersCommon__ext4O__pcellT312_r16__supported
  end.
Lemma MeasAndMobParametersCommon__ext4O__pcellT312_r16__F1F2 : forall x : MeasAndMobParametersCommon__ext4O__pcellT312_r16__Type, (MeasAndMobParametersCommon__ext4O__pcellT312_r16__F1 x <= 0) /\ MeasAndMobParametersCommon__ext4O__pcellT312_r16__F2 (MeasAndMobParametersCommon__ext4O__pcellT312_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext4O__pcellT312_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext4O__pcellT312_r16__F1 (MeasAndMobParametersCommon__ext4O__pcellT312_r16__F2 y) = y. enum_solve H y. Qed.

Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__Type := bit_string_fixed.
Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Record MeasAndMobParametersCommon__ext4O__Type : Set :=
  make__MeasAndMobParametersCommon__ext4O__Type {
    MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16 : option MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Type ;
    MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16 : option MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Type ;
    MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16 : option MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Type ;
    MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16 : option MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__Type ;
    MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16 : option MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Type ;
    MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16 : option MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Type ;
    MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16 : option MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Type ;
    MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16 : option MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Type ;
    MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16 : option MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Type ;
    MeasAndMobParametersCommon__ext4O__dummy : option MeasAndMobParametersCommon__ext4O__dummy__Type ;
    MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16 : option MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Type ;
    MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16 : option MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Type ;
    MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16 : option MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Type ;
    MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16 : option MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Type ;
    MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16 : option MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Type ;
    MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16 : option MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Type ;
    MeasAndMobParametersCommon__ext4O__pcellT312_r16 : option MeasAndMobParametersCommon__ext4O__pcellT312_r16__Type ;
    MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16 : option MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__Type ;
}.
Definition MeasAndMobParametersCommon__ext4O__list := (
 Opt MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Type MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Type MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Type MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__Type MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Type MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Type MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Type MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Type MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Type MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__dummy__Type MeasAndMobParametersCommon__ext4O__dummy__cond ::
 Opt MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Type MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Type MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Type MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Type MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Type MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Type MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__pcellT312_r16__Type MeasAndMobParametersCommon__ext4O__pcellT312_r16__cond ::
 Opt MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__Type MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext4O__cond z := 
  opt_cond MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__cond (MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__cond (MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__cond (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__cond (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__cond (MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__cond (MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__cond (MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__cond (MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__dummy__cond (MeasAndMobParametersCommon__ext4O__dummy z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__cond (MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__cond (MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__cond (MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__cond (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__cond (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__cond (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__pcellT312_r16__cond (MeasAndMobParametersCommon__ext4O__pcellT312_r16 z) /\
  opt_cond MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__cond (MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16 z) /\
  True.

Definition MeasAndMobParametersCommon__ext4__Type := MeasAndMobParametersCommon__ext4O__Type.
Definition MeasAndMobParametersCommon__ext4__cond := MeasAndMobParametersCommon__ext4O__cond.

Inductive MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Type, (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F2 (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F1 (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Type, (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F2 (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F1 (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F2 y) = y. enum_solve H y. Qed.


Inductive MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type : Set :=
  | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17 : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Type -> MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type
  | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17 : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Type -> MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type
.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list : list typ := (
typ_cons MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Type MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__cond ::
typ_cons MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Type MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__cond (c : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type) := 
  match c with
  | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17 t => MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__cond t 
  | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17 t => MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__cond t 
  end.

Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__len_helper1 : to_bit_sz (length MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__len_helper2 : 2 <= length2 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list.
 simpl. lia. Qed.
Inductive MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Type, (MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F2 (MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F1 (MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Type, (MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F2 (MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F1 (MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Type, (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F2 (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F1 (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F2 y) = y. enum_solve H y. Qed.

Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__Type := bit_string_fixed.
Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 24 /\ bit_string_len_prop (fst z) (snd z)).
Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__Type := bit_string_fixed.
Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 24 /\ bit_string_len_prop (fst z) (snd z)).
Inductive MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Type, (MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F2 (MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F1 (MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Type, (MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F2 (MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F1 (MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Type, (MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F2 (MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F1 (MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Type, (MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F2 (MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F1 (MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Type, (MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F2 (MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F1 (MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Type, (MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F2 (MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F1 (MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__n2
.
Definition MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__n2 => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__n2
  | _ => MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__n2
  end.
Lemma MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Type, (MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F2 (MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F1 (MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Type, (MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F2 (MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F1 (MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Type, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F2 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F1 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Type, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F2 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F1 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Type, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F2 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F1 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Type, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F2 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F1 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__supported
.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__supported
  | _ => MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Type, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F2 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F1 (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersCommon__ext5O__Type : Set :=
  make__MeasAndMobParametersCommon__ext5O__Type {
    MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17 : option MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type ;
    MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17 : option MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Type ;
    MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17 : option MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Type ;
    MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17 : option MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Type ;
    MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17 : option MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__Type ;
    MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17 : option MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__Type ;
    MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17 : option MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Type ;
    MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17 : option MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Type ;
    MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17 : option MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Type ;
    MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17 : option MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Type ;
    MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17 : option MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Type ;
    MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17 : option MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Type ;
    MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17 : option MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Type ;
    MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17 : option MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Type ;
    MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17 : option MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Type ;
    MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17 : option MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Type ;
    MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17 : option MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Type ;
    MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17 : option MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Type ;
    MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17 : option MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Type ;
}.
Definition MeasAndMobParametersCommon__ext5O__list := (
 Opt MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Type MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Type MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Type MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__Type MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__Type MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Type MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Type MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Type MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Type MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Type MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Type MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Type MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Type MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Type MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Type MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Type MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Type MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__cond ::
 Opt MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Type MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext5O__cond z := 
  opt_cond MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__cond (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__cond (MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__cond (MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__cond (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__cond (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__cond (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__cond (MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__cond (MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__cond (MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__cond (MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__cond (MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__cond (MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__cond (MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__cond (MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__cond (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__cond (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__cond (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__cond (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__cond (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17 z) /\
  True.

Definition MeasAndMobParametersCommon__ext5__Type := MeasAndMobParametersCommon__ext5O__Type.
Definition MeasAndMobParametersCommon__ext5__cond := MeasAndMobParametersCommon__ext5O__cond.

Inductive MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__n4
.
Definition MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__n4 => 0
  end.
Definition MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__n4
  | _ => MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__n4
  end.
Lemma MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Type, (MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F2 (MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F1 (MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__supported
.
Definition MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__supported
  | _ => MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Type, (MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F2 (MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F1 (MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__supported
.
Definition MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__supported
  | _ => MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Type, (MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F2 (MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F1 (MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__supported
.
Definition MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__supported
  | _ => MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Type, (MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F2 (MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F1 (MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersCommon__ext6O__Type : Set :=
  make__MeasAndMobParametersCommon__ext6O__Type {
    MeasAndMobParametersCommon__ext6O__parallelSMTC_r17 : option MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Type ;
    MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17 : option MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Type ;
    MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17 : option MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Type ;
    MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17 : option MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Type ;
}.
Definition MeasAndMobParametersCommon__ext6O__list := (
 Opt MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Type MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__cond ::
 Opt MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Type MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__cond ::
 Opt MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Type MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__cond ::
 Opt MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Type MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext6O__cond z := 
  opt_cond MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__cond (MeasAndMobParametersCommon__ext6O__parallelSMTC_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__cond (MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__cond (MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__cond (MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17 z) /\
  True.

Definition MeasAndMobParametersCommon__ext6__Type := MeasAndMobParametersCommon__ext6O__Type.
Definition MeasAndMobParametersCommon__ext6__cond := MeasAndMobParametersCommon__ext6O__cond.

Inductive MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Type : Set :=
 | MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__supported
.
Definition MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__cond := (fun (_ : MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Type) => True).
Lemma MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__nat__helper.

Definition MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F1 t :=
  match t with
  | MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__supported => 0
  end.
Definition MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__supported
  | _ => MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__supported
  end.
Lemma MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F1F2 : forall x : MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Type, (MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F1 x <= 0) /\ MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F2 (MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F1 (MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__Type := Z.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__cond := (fun z => (1 <= z <= 32)%Z).
Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__Type := Z.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__cond := (fun z => (1 <= z <= 32)%Z).
Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__Type := Z.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__cond := (fun z => (1 <= z <= 32)%Z).
Record MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Type : Set :=
  make__MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Type {
    MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17 : option Z ;
    MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17 : option Z ;
    MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17 : option Z ;
}.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list := (
 Opt Z MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__cond ::
 Opt Z MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__cond ::
 Opt Z MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond z := 
  opt_cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__cond (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__cond (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__cond (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17 z) /\
  True.

Record MeasAndMobParametersCommon__ext7O__Type : Set :=
  make__MeasAndMobParametersCommon__ext7O__Type {
    MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17 : option MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Type ;
    MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17 : option MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Type ;
}.
Definition MeasAndMobParametersCommon__ext7O__list := (
 Opt MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Type MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__cond ::
 Opt MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Type MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext7O__cond z := 
  opt_cond MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__cond (MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17 z) /\
  opt_cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17 z) /\
  True.

Definition MeasAndMobParametersCommon__ext7__Type := MeasAndMobParametersCommon__ext7O__Type.
Definition MeasAndMobParametersCommon__ext7__cond := MeasAndMobParametersCommon__ext7O__cond.

Record MeasAndMobParametersCommon__Type : Set :=
  make__MeasAndMobParametersCommon__Type {
    MeasAndMobParametersCommon__supportedGapPattern : option MeasAndMobParametersCommon__supportedGapPattern__Type ;
    MeasAndMobParametersCommon__ssb_RLM : option MeasAndMobParametersCommon__ssb_RLM__Type ;
    MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM : option MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Type ;
    MeasAndMobParametersCommon__ext0 : option MeasAndMobParametersCommon__ext0__Type ;
    MeasAndMobParametersCommon__ext1 : option MeasAndMobParametersCommon__ext1__Type ;
    MeasAndMobParametersCommon__ext2 : option MeasAndMobParametersCommon__ext2__Type ;
    MeasAndMobParametersCommon__ext3 : option MeasAndMobParametersCommon__ext3__Type ;
    MeasAndMobParametersCommon__ext4 : option MeasAndMobParametersCommon__ext4__Type ;
    MeasAndMobParametersCommon__ext5 : option MeasAndMobParametersCommon__ext5__Type ;
    MeasAndMobParametersCommon__ext6 : option MeasAndMobParametersCommon__ext6__Type ;
    MeasAndMobParametersCommon__ext7 : option MeasAndMobParametersCommon__ext7__Type ;
}.
Definition MeasAndMobParametersCommon__root_list : list seq_elem := (
 Opt MeasAndMobParametersCommon__supportedGapPattern__Type MeasAndMobParametersCommon__supportedGapPattern__cond ::
 Opt MeasAndMobParametersCommon__ssb_RLM__Type MeasAndMobParametersCommon__ssb_RLM__cond ::
 Opt MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Type MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__cond ::
 nil).
Definition MeasAndMobParametersCommon__ext_list : list typ := (
  typ_cons MeasAndMobParametersCommon__ext0__Type MeasAndMobParametersCommon__ext0__cond ::
  typ_cons MeasAndMobParametersCommon__ext1__Type MeasAndMobParametersCommon__ext1__cond ::
  typ_cons MeasAndMobParametersCommon__ext2__Type MeasAndMobParametersCommon__ext2__cond ::
  typ_cons MeasAndMobParametersCommon__ext3__Type MeasAndMobParametersCommon__ext3__cond ::
  typ_cons MeasAndMobParametersCommon__ext4__Type MeasAndMobParametersCommon__ext4__cond ::
  typ_cons MeasAndMobParametersCommon__ext5__Type MeasAndMobParametersCommon__ext5__cond ::
  typ_cons MeasAndMobParametersCommon__ext6__Type MeasAndMobParametersCommon__ext6__cond ::
  typ_cons MeasAndMobParametersCommon__ext7__Type MeasAndMobParametersCommon__ext7__cond ::
  nil).
Definition MeasAndMobParametersCommon__cond (z : MeasAndMobParametersCommon__Type) := 
(  opt_cond MeasAndMobParametersCommon__supportedGapPattern__cond (MeasAndMobParametersCommon__supportedGapPattern z) /\
  opt_cond MeasAndMobParametersCommon__ssb_RLM__cond (MeasAndMobParametersCommon__ssb_RLM z) /\
  opt_cond MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__cond (MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM z) /\
  True) /\ 
(  opt_cond MeasAndMobParametersCommon__ext0__cond (MeasAndMobParametersCommon__ext0 z) /\
  opt_cond MeasAndMobParametersCommon__ext1__cond (MeasAndMobParametersCommon__ext1 z) /\
  opt_cond MeasAndMobParametersCommon__ext2__cond (MeasAndMobParametersCommon__ext2 z) /\
  opt_cond MeasAndMobParametersCommon__ext3__cond (MeasAndMobParametersCommon__ext3 z) /\
  opt_cond MeasAndMobParametersCommon__ext4__cond (MeasAndMobParametersCommon__ext4 z) /\
  opt_cond MeasAndMobParametersCommon__ext5__cond (MeasAndMobParametersCommon__ext5 z) /\
  opt_cond MeasAndMobParametersCommon__ext6__cond (MeasAndMobParametersCommon__ext6 z) /\
  opt_cond MeasAndMobParametersCommon__ext7__cond (MeasAndMobParametersCommon__ext7 z) /\
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
Definition MeasAndMobParametersCommon__supportedGapPattern__Format : T_Format MeasAndMobParametersCommon__supportedGapPattern__Type MeasAndMobParametersCommon__supportedGapPattern__cond := (* Eval compute in *) bit_string_fixed_format 22.
Opaque MeasAndMobParametersCommon__supportedGapPattern__cond MeasAndMobParametersCommon__supportedGapPattern__Format.

Definition MeasAndMobParametersCommon__ssb_RLM__Format : T_Format MeasAndMobParametersCommon__ssb_RLM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ssb_RLM__nat__Format MeasAndMobParametersCommon__ssb_RLM__F1 MeasAndMobParametersCommon__ssb_RLM__F2 MeasAndMobParametersCommon__ssb_RLM__F1F2 MeasAndMobParametersCommon__ssb_RLM__F2F1.

Opaque MeasAndMobParametersCommon__ssb_RLM__cond MeasAndMobParametersCommon__ssb_RLM__Format.

Definition MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Format : T_Format MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__nat__Format MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F1 MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F2 MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F1F2 MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__F2F1.

Opaque MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__cond MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Format.

Definition MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Format : T_Format MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__nat__Format MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F1 MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F2 MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F1F2 MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__F2F1.

Opaque MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__cond MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Format.

Definition MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Format : T_Format MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__nat__Format MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F1 MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F2 MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F1F2 MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__F2F1.

Opaque MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__cond MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Format.

Definition MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Format : T_Format MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__nat__Format MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F1 MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F2 MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F1F2 MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__F2F1.

Opaque MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__cond MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Format.

Definition MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Format : T_Format MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__nat__Format MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F1 MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F2 MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F1F2 MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__F2F1.

Opaque MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__cond MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Format.


Definition MeasAndMobParametersCommon__ext0O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext0O__list.
Definition MeasAndMobParametersCommon__ext0O__Format_list : MeasAndMobParametersCommon__ext0O__Format_Type :=
  (MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport__Format, (MeasAndMobParametersCommon__ext0O__handoverFDD_TDD__Format, (MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting__Format, (MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting__Format, unit_format)))).
Definition MeasAndMobParametersCommon__ext0O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext0O__list MeasAndMobParametersCommon__ext0O__Format_list.
Definition MeasAndMobParametersCommon__ext0O__F1 z :=
  (MeasAndMobParametersCommon__ext0O__eventB_MeasAndReport z, (MeasAndMobParametersCommon__ext0O__handoverFDD_TDD z, (MeasAndMobParametersCommon__ext0O__eutra_CGI_Reporting z, (MeasAndMobParametersCommon__ext0O__nr_CGI_Reporting z, tt)))).
Definition MeasAndMobParametersCommon__ext0O__F2 (y : seq_type MeasAndMobParametersCommon__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasAndMobParametersCommon__ext0O__Type i0 i1 i2 i3
  end.
Lemma MeasAndMobParametersCommon__ext0O__F1F2_cond (z : MeasAndMobParametersCommon__ext0O__Type)
  : MeasAndMobParametersCommon__ext0O__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext0O__list (MeasAndMobParametersCommon__ext0O__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext0O__F1F2_cond2 (z : MeasAndMobParametersCommon__ext0O__Type)
 : MeasAndMobParametersCommon__ext0O__F2 (MeasAndMobParametersCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext0O__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext0O__list)
  : seq_cond MeasAndMobParametersCommon__ext0O__list y ->
 (MeasAndMobParametersCommon__ext0O__cond (MeasAndMobParametersCommon__ext0O__F2 y)) /\  MeasAndMobParametersCommon__ext0O__F1 (MeasAndMobParametersCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext0O__Format : T_Format MeasAndMobParametersCommon__ext0O__Type MeasAndMobParametersCommon__ext0O__cond :=
        proj2_format  MeasAndMobParametersCommon__ext0O__cond MeasAndMobParametersCommon__ext0O__list__Format
    MeasAndMobParametersCommon__ext0O__F1 MeasAndMobParametersCommon__ext0O__F2 MeasAndMobParametersCommon__ext0O__F1F2_cond  MeasAndMobParametersCommon__ext0O__F1F2_cond2 MeasAndMobParametersCommon__ext0O__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext0O__cond MeasAndMobParametersCommon__ext0O__Format.

Definition MeasAndMobParametersCommon__ext0__check_all_none (b : MeasAndMobParametersCommon__ext0O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersCommon__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersCommon__ext0__Format : T_Format MeasAndMobParametersCommon__ext0__Type MeasAndMobParametersCommon__ext0__cond :=
  restrict_add_format MeasAndMobParametersCommon__ext0__check_all_none MeasAndMobParametersCommon__ext0O__Format.

Opaque MeasAndMobParametersCommon__ext0__cond MeasAndMobParametersCommon__ext0__Format.

Definition MeasAndMobParametersCommon__ext1O__independentGapConfig__Format : T_Format MeasAndMobParametersCommon__ext1O__independentGapConfig__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext1O__independentGapConfig__nat__Format MeasAndMobParametersCommon__ext1O__independentGapConfig__F1 MeasAndMobParametersCommon__ext1O__independentGapConfig__F2 MeasAndMobParametersCommon__ext1O__independentGapConfig__F1F2 MeasAndMobParametersCommon__ext1O__independentGapConfig__F2F1.

Opaque MeasAndMobParametersCommon__ext1O__independentGapConfig__cond MeasAndMobParametersCommon__ext1O__independentGapConfig__Format.

Definition MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Format : T_Format MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__nat__Format MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F1 MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F2 MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F1F2 MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__F2F1.

Opaque MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__cond MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Format.

Definition MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Format : T_Format MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__nat__Format MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F1 MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F2 MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F1F2 MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__F2F1.

Opaque MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__cond MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Format.

Definition MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Format : T_Format MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__nat__Format MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F1 MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F2 MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F1F2 MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__F2F1.

Opaque MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__cond MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Format.


Definition MeasAndMobParametersCommon__ext1O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext1O__list.
Definition MeasAndMobParametersCommon__ext1O__Format_list : MeasAndMobParametersCommon__ext1O__Format_Type :=
  (MeasAndMobParametersCommon__ext1O__independentGapConfig__Format, (MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport__Format, (MeasAndMobParametersCommon__ext1O__handoverFR1_FR2__Format, (MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR__Format, unit_format)))).
Definition MeasAndMobParametersCommon__ext1O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext1O__list MeasAndMobParametersCommon__ext1O__Format_list.
Definition MeasAndMobParametersCommon__ext1O__F1 z :=
  (MeasAndMobParametersCommon__ext1O__independentGapConfig z, (MeasAndMobParametersCommon__ext1O__periodicEUTRA_MeasAndReport z, (MeasAndMobParametersCommon__ext1O__handoverFR1_FR2 z, (MeasAndMobParametersCommon__ext1O__maxNumberCSI_RS_RRM_RS_SINR z, tt)))).
Definition MeasAndMobParametersCommon__ext1O__F2 (y : seq_type MeasAndMobParametersCommon__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasAndMobParametersCommon__ext1O__Type i0 i1 i2 i3
  end.
Lemma MeasAndMobParametersCommon__ext1O__F1F2_cond (z : MeasAndMobParametersCommon__ext1O__Type)
  : MeasAndMobParametersCommon__ext1O__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext1O__list (MeasAndMobParametersCommon__ext1O__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext1O__F1F2_cond2 (z : MeasAndMobParametersCommon__ext1O__Type)
 : MeasAndMobParametersCommon__ext1O__F2 (MeasAndMobParametersCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext1O__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext1O__list)
  : seq_cond MeasAndMobParametersCommon__ext1O__list y ->
 (MeasAndMobParametersCommon__ext1O__cond (MeasAndMobParametersCommon__ext1O__F2 y)) /\  MeasAndMobParametersCommon__ext1O__F1 (MeasAndMobParametersCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext1O__Format : T_Format MeasAndMobParametersCommon__ext1O__Type MeasAndMobParametersCommon__ext1O__cond :=
        proj2_format  MeasAndMobParametersCommon__ext1O__cond MeasAndMobParametersCommon__ext1O__list__Format
    MeasAndMobParametersCommon__ext1O__F1 MeasAndMobParametersCommon__ext1O__F2 MeasAndMobParametersCommon__ext1O__F1F2_cond  MeasAndMobParametersCommon__ext1O__F1F2_cond2 MeasAndMobParametersCommon__ext1O__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext1O__cond MeasAndMobParametersCommon__ext1O__Format.

Definition MeasAndMobParametersCommon__ext1__check_all_none (b : MeasAndMobParametersCommon__ext1O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersCommon__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersCommon__ext1__Format : T_Format MeasAndMobParametersCommon__ext1__Type MeasAndMobParametersCommon__ext1__cond :=
  restrict_add_format MeasAndMobParametersCommon__ext1__check_all_none MeasAndMobParametersCommon__ext1O__Format.

Opaque MeasAndMobParametersCommon__ext1__cond MeasAndMobParametersCommon__ext1__Format.

Definition MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Format : T_Format MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__nat__Format MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F1 MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F2 MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F1F2 MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__F2F1.

Opaque MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__cond MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Format.


Definition MeasAndMobParametersCommon__ext2O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext2O__list.
Definition MeasAndMobParametersCommon__ext2O__Format_list : MeasAndMobParametersCommon__ext2O__Format_Type :=
  (MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC__Format, unit_format).
Definition MeasAndMobParametersCommon__ext2O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext2O__list MeasAndMobParametersCommon__ext2O__Format_list.
Definition MeasAndMobParametersCommon__ext2O__F1 z :=
  (MeasAndMobParametersCommon__ext2O__nr_CGI_Reporting_ENDC z, tt).
Definition MeasAndMobParametersCommon__ext2O__F2 (y : seq_type MeasAndMobParametersCommon__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__MeasAndMobParametersCommon__ext2O__Type i0
  end.
Lemma MeasAndMobParametersCommon__ext2O__F1F2_cond (z : MeasAndMobParametersCommon__ext2O__Type)
  : MeasAndMobParametersCommon__ext2O__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext2O__list (MeasAndMobParametersCommon__ext2O__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext2O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext2O__F1F2_cond2 (z : MeasAndMobParametersCommon__ext2O__Type)
 : MeasAndMobParametersCommon__ext2O__F2 (MeasAndMobParametersCommon__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext2O__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext2O__list)
  : seq_cond MeasAndMobParametersCommon__ext2O__list y ->
 (MeasAndMobParametersCommon__ext2O__cond (MeasAndMobParametersCommon__ext2O__F2 y)) /\  MeasAndMobParametersCommon__ext2O__F1 (MeasAndMobParametersCommon__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext2O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext2O__Format : T_Format MeasAndMobParametersCommon__ext2O__Type MeasAndMobParametersCommon__ext2O__cond :=
        proj2_format  MeasAndMobParametersCommon__ext2O__cond MeasAndMobParametersCommon__ext2O__list__Format
    MeasAndMobParametersCommon__ext2O__F1 MeasAndMobParametersCommon__ext2O__F2 MeasAndMobParametersCommon__ext2O__F1F2_cond  MeasAndMobParametersCommon__ext2O__F1F2_cond2 MeasAndMobParametersCommon__ext2O__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext2O__cond MeasAndMobParametersCommon__ext2O__Format.

Definition MeasAndMobParametersCommon__ext2__check_all_none (b : MeasAndMobParametersCommon__ext2O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersCommon__ext2O__Type None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersCommon__ext2__Format : T_Format MeasAndMobParametersCommon__ext2__Type MeasAndMobParametersCommon__ext2__cond :=
  restrict_add_format MeasAndMobParametersCommon__ext2__check_all_none MeasAndMobParametersCommon__ext2O__Format.

Opaque MeasAndMobParametersCommon__ext2__cond MeasAndMobParametersCommon__ext2__Format.

Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Format : T_Format MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__nat__Format MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F1 MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F2 MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F1F2 MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__F2F1.

Opaque MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__cond MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Format.

Definition MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Format : T_Format MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__nat__Format MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F1 MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F2 MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F1F2 MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__F2F1.

Opaque MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__cond MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Format.

Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Format : T_Format MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__nat__Format MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F1 MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F2 MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F1F2 MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__F2F1.

Opaque MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__cond MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Format.

Definition MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Format : T_Format MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__nat__Format MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F1 MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F2 MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F1F2 MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__F2F1.

Opaque MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__cond MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Format.


Definition MeasAndMobParametersCommon__ext3O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext3O__list.
Definition MeasAndMobParametersCommon__ext3O__Format_list : MeasAndMobParametersCommon__ext3O__Format_Type :=
  (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC__Format, (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC__Format, (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC__Format, (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC__Format, unit_format)))).
Definition MeasAndMobParametersCommon__ext3O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext3O__list MeasAndMobParametersCommon__ext3O__Format_list.
Definition MeasAndMobParametersCommon__ext3O__F1 z :=
  (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NEDC z, (MeasAndMobParametersCommon__ext3O__eutra_CGI_Reporting_NRDC z, (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NEDC z, (MeasAndMobParametersCommon__ext3O__nr_CGI_Reporting_NRDC z, tt)))).
Definition MeasAndMobParametersCommon__ext3O__F2 (y : seq_type MeasAndMobParametersCommon__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasAndMobParametersCommon__ext3O__Type i0 i1 i2 i3
  end.
Lemma MeasAndMobParametersCommon__ext3O__F1F2_cond (z : MeasAndMobParametersCommon__ext3O__Type)
  : MeasAndMobParametersCommon__ext3O__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext3O__list (MeasAndMobParametersCommon__ext3O__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext3O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext3O__F1F2_cond2 (z : MeasAndMobParametersCommon__ext3O__Type)
 : MeasAndMobParametersCommon__ext3O__F2 (MeasAndMobParametersCommon__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext3O__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext3O__list)
  : seq_cond MeasAndMobParametersCommon__ext3O__list y ->
 (MeasAndMobParametersCommon__ext3O__cond (MeasAndMobParametersCommon__ext3O__F2 y)) /\  MeasAndMobParametersCommon__ext3O__F1 (MeasAndMobParametersCommon__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext3O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext3O__Format : T_Format MeasAndMobParametersCommon__ext3O__Type MeasAndMobParametersCommon__ext3O__cond :=
        proj2_format  MeasAndMobParametersCommon__ext3O__cond MeasAndMobParametersCommon__ext3O__list__Format
    MeasAndMobParametersCommon__ext3O__F1 MeasAndMobParametersCommon__ext3O__F2 MeasAndMobParametersCommon__ext3O__F1F2_cond  MeasAndMobParametersCommon__ext3O__F1F2_cond2 MeasAndMobParametersCommon__ext3O__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext3O__cond MeasAndMobParametersCommon__ext3O__Format.

Definition MeasAndMobParametersCommon__ext3__check_all_none (b : MeasAndMobParametersCommon__ext3O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersCommon__ext3O__Type None None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersCommon__ext3__Format : T_Format MeasAndMobParametersCommon__ext3__Type MeasAndMobParametersCommon__ext3__cond :=
  restrict_add_format MeasAndMobParametersCommon__ext3__check_all_none MeasAndMobParametersCommon__ext3O__Format.

Opaque MeasAndMobParametersCommon__ext3__cond MeasAndMobParametersCommon__ext3__Format.

Definition MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__nat__Format MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F1 MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F2 MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F1F2 MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__cond MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__nat__Format MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F1 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F2 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F1F2 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__nat__Format MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F1 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F2 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F1F2 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Format.


Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Format_list : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Format_Type :=
  (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16__Format, (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16__Format, unit_format)).
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Format_list.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1 z :=
  (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFDD_TDD_r16 z, (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__condHandoverFR1_FR2_r16 z, tt)).
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F2 (y : seq_type MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Type i0 i1
  end.
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1F2_cond (z : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Type)
  : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1F2_cond2 (z : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Type)
 : MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F2 (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list)
  : seq_cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list y ->
 (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F2 y)) /\  MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1 (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Type MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond :=
        proj2_format  MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__list__Format
    MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F2 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1F2_cond  MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F1F2_cond2 MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__cond MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__nat__Format MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F1 MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F2 MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F1F2 MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__cond MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__Type MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__cond MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__nat__Format MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F1 MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F2 MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F1F2 MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__cond MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__nat__Format MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F1 MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F2 MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F1F2 MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__cond MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__nat__Format MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F1 MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F2 MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F1F2 MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__cond MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__nat__Format MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F1 MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F2 MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F1F2 MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__cond MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__nat__Format MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F1 MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F2 MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F1F2 MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__cond MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__dummy__Format : T_Format MeasAndMobParametersCommon__ext4O__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__dummy__nat__Format MeasAndMobParametersCommon__ext4O__dummy__F1 MeasAndMobParametersCommon__ext4O__dummy__F2 MeasAndMobParametersCommon__ext4O__dummy__F1F2 MeasAndMobParametersCommon__ext4O__dummy__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__dummy__cond MeasAndMobParametersCommon__ext4O__dummy__Format.

Definition MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__nat__Format MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F1 MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F2 MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F1F2 MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__cond MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__nat__Format MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F1 MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F2 MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F1F2 MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__cond MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__nat__Format MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F1 MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F2 MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F1F2 MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__cond MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__nat__Format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F1 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F2 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F1F2 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__cond MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__nat__Format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F1 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F2 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F1F2 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__cond MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__nat__Format MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F1 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F2 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F1F2 MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__cond MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__pcellT312_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__pcellT312_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext4O__pcellT312_r16__nat__Format MeasAndMobParametersCommon__ext4O__pcellT312_r16__F1 MeasAndMobParametersCommon__ext4O__pcellT312_r16__F2 MeasAndMobParametersCommon__ext4O__pcellT312_r16__F1F2 MeasAndMobParametersCommon__ext4O__pcellT312_r16__F2F1.

Opaque MeasAndMobParametersCommon__ext4O__pcellT312_r16__cond MeasAndMobParametersCommon__ext4O__pcellT312_r16__Format.

Definition MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__Format : T_Format MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__Type MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__cond MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__Format.


Definition MeasAndMobParametersCommon__ext4O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext4O__list.
Definition MeasAndMobParametersCommon__ext4O__Format_list : MeasAndMobParametersCommon__ext4O__Format_Type :=
  (MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16__Format, (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16__Format, (MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16__Format, (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16__Format, (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16__Format, (MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16__Format, (MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16__Format, (MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16__Format, (MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16__Format, (MeasAndMobParametersCommon__ext4O__dummy__Format, (MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16__Format, (MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16__Format, (MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16__Format, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16__Format, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16__Format, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16__Format, (MeasAndMobParametersCommon__ext4O__pcellT312_r16__Format, (MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16__Format, unit_format)))))))))))))))))).
Definition MeasAndMobParametersCommon__ext4O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext4O__list MeasAndMobParametersCommon__ext4O__Format_list.
Definition MeasAndMobParametersCommon__ext4O__F1 z :=
  (MeasAndMobParametersCommon__ext4O__reportAddNeighMeasForPeriodic_r16 z, (MeasAndMobParametersCommon__ext4O__condHandoverParametersCommon_r16 z, (MeasAndMobParametersCommon__ext4O__nr_NeedForGap_Reporting_r16 z, (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_r16 z, (MeasAndMobParametersCommon__ext4O__supportedGapPattern_NRonly_NEDC_r16 z, (MeasAndMobParametersCommon__ext4O__maxNumberCLI_RSSI_r16 z, (MeasAndMobParametersCommon__ext4O__maxNumberCLI_SRS_RSRP_r16 z, (MeasAndMobParametersCommon__ext4O__maxNumberPerSlotCLI_SRS_RSRP_r16 z, (MeasAndMobParametersCommon__ext4O__mfbi_IAB_r16 z, (MeasAndMobParametersCommon__ext4O__dummy z, (MeasAndMobParametersCommon__ext4O__nr_CGI_Reporting_NPN_r16 z, (MeasAndMobParametersCommon__ext4O__idleInactiveEUTRA_MeasReport_r16 z, (MeasAndMobParametersCommon__ext4O__idleInactive_ValidityArea_r16 z, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_r16 z, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NEDC_r16 z, (MeasAndMobParametersCommon__ext4O__eutra_AutonomousGaps_NRDC_r16 z, (MeasAndMobParametersCommon__ext4O__pcellT312_r16 z, (MeasAndMobParametersCommon__ext4O__supportedGapPattern_r16 z, tt)))))))))))))))))).
Definition MeasAndMobParametersCommon__ext4O__F2 (y : seq_type MeasAndMobParametersCommon__ext4O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, _))))))))))))))))))=>
    make__MeasAndMobParametersCommon__ext4O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17
  end.
Lemma MeasAndMobParametersCommon__ext4O__F1F2_cond (z : MeasAndMobParametersCommon__ext4O__Type)
  : MeasAndMobParametersCommon__ext4O__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext4O__list (MeasAndMobParametersCommon__ext4O__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext4O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext4O__F1F2_cond2 (z : MeasAndMobParametersCommon__ext4O__Type)
 : MeasAndMobParametersCommon__ext4O__F2 (MeasAndMobParametersCommon__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext4O__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext4O__list)
  : seq_cond MeasAndMobParametersCommon__ext4O__list y ->
 (MeasAndMobParametersCommon__ext4O__cond (MeasAndMobParametersCommon__ext4O__F2 y)) /\  MeasAndMobParametersCommon__ext4O__F1 (MeasAndMobParametersCommon__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext4O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext4O__Format : T_Format MeasAndMobParametersCommon__ext4O__Type MeasAndMobParametersCommon__ext4O__cond :=
        proj2_format  MeasAndMobParametersCommon__ext4O__cond MeasAndMobParametersCommon__ext4O__list__Format
    MeasAndMobParametersCommon__ext4O__F1 MeasAndMobParametersCommon__ext4O__F2 MeasAndMobParametersCommon__ext4O__F1F2_cond  MeasAndMobParametersCommon__ext4O__F1F2_cond2 MeasAndMobParametersCommon__ext4O__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext4O__cond MeasAndMobParametersCommon__ext4O__Format.

Definition MeasAndMobParametersCommon__ext4__check_all_none (b : MeasAndMobParametersCommon__ext4O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersCommon__ext4O__Type None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersCommon__ext4__Format : T_Format MeasAndMobParametersCommon__ext4__Type MeasAndMobParametersCommon__ext4__cond :=
  restrict_add_format MeasAndMobParametersCommon__ext4__check_all_none MeasAndMobParametersCommon__ext4O__Format.

Opaque MeasAndMobParametersCommon__ext4__cond MeasAndMobParametersCommon__ext4__Format.

Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__nat__Format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F1 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F2 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F1F2 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__cond MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__nat__Format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F1 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F2 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F1F2 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__cond MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Format.


Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Format_Type := Eval cbn in get_formats MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Format_list : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Format_Type :=
  (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Format, (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Format, unit__Format)).
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list__Format := Eval compute in choice_format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__len_helper1 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__len_helper2  MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Format_list.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F1 (z : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type) : (choice MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list) :=
  match z with
   | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17 t => existT _ 0 t
  | MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17 t => existT _ 1 t
  end.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__g := (fun n => typ_set (get_nth_typ MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list n)).
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F2 (y : choice MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list) : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__g n -> MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type) with
    | 0 => fun (t : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17__Type) => MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_OnlyMeasGap_r17 t 
    | 1 => fun (t : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17__Type) => MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__concurrentPerUE_PerFRCombMeasGap_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type with end) n0
           end t0).

Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__helper2 :  forall (y : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type), MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__cond y -> choice_cond MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__helper3 :  forall (y : MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type), MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F2 (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__helper4 : (forall b : choice MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list, choice_cond MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list b -> MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__cond (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F2 b) /\ MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F1 (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F1 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F2.
Definition MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Type MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__cond :=
  (* Eval compute in *) proj2_format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__cond MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__list__Format MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F1 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__F2 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__helper2 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__helper3 MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__helper4.
Opaque MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__cond MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__nat__Format MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F1 MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F2 MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F1F2 MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__cond MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__nat__Format MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F1 MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F2 MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F1F2 MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__cond MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__nat__Format MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F1 MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F2 MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F1F2 MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__cond MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__Type MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__cond := (* Eval compute in *) bit_string_fixed_format 24.
Opaque MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__cond MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__Type MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__cond := (* Eval compute in *) bit_string_fixed_format 24.
Opaque MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__cond MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__nat__Format MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F1 MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F2 MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F1F2 MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__cond MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__nat__Format MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F1 MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F2 MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F1F2 MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__cond MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__nat__Format MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F1 MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F2 MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F1F2 MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__cond MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__nat__Format MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F1 MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F2 MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F1F2 MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__cond MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__nat__Format MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F1 MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F2 MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F1F2 MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__cond MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__nat__Format MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F1 MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F2 MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F1F2 MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__cond MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__nat__Format MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F1 MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F2 MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F1F2 MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__cond MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__nat__Format MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F1 MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F2 MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F1F2 MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__cond MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__nat__Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F1 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F1F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__nat__Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F1 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F1F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__nat__Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F1 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F1F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__nat__Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F1 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F1F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Format.

Definition MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Format : T_Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__nat__Format MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F1 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F1F2 MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__cond MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Format.


Definition MeasAndMobParametersCommon__ext5O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext5O__list.
Definition MeasAndMobParametersCommon__ext5O__Format_list : MeasAndMobParametersCommon__ext5O__Format_Type :=
  (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17__Format, (MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17__Format, (MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17__Format, (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17__Format, (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17__Format, (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17__Format, (MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17__Format, (MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17__Format, (MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17__Format, (MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17__Format, (MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17__Format, (MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17__Format, (MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17__Format, (MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17__Format, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17__Format, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17__Format, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17__Format, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17__Format, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17__Format, unit_format))))))))))))))))))).
Definition MeasAndMobParametersCommon__ext5O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext5O__list MeasAndMobParametersCommon__ext5O__Format_list.
Definition MeasAndMobParametersCommon__ext5O__F1 z :=
  (MeasAndMobParametersCommon__ext5O__concurrentMeasGap_r17 z, (MeasAndMobParametersCommon__ext5O__nr_NeedForGapNCSG_Reporting_r17 z, (MeasAndMobParametersCommon__ext5O__eutra_NeedForGapNCSG_Reporting_r17 z, (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPerFR_r17 z, (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapPatterns_r17 z, (MeasAndMobParametersCommon__ext5O__ncsg_MeasGapNR_Patterns_r17 z, (MeasAndMobParametersCommon__ext5O__preconfiguredUE_AutonomousMeasGap_r17 z, (MeasAndMobParametersCommon__ext5O__preconfiguredNW_ControlledMeasGap_r17 z, (MeasAndMobParametersCommon__ext5O__handoverFR1_FR2_2_r17 z, (MeasAndMobParametersCommon__ext5O__handoverFR2_1_FR2_2_r17 z, (MeasAndMobParametersCommon__ext5O__independentGapConfigPRS_r17 z, (MeasAndMobParametersCommon__ext5O__rrm_RelaxationRRC_ConnectedRedCap_r17 z, (MeasAndMobParametersCommon__ext5O__parallelMeasurementGap_r17 z, (MeasAndMobParametersCommon__ext5O__condHandoverWithSCG_NRDC_r17 z, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_r17 z, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_ENDC_r17 z, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NEDC_r17 z, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NRDC_r17 z, (MeasAndMobParametersCommon__ext5O__gNB_ID_LengthReporting_NPN_r17 z, tt))))))))))))))))))).
Definition MeasAndMobParametersCommon__ext5O__F2 (y : seq_type MeasAndMobParametersCommon__ext5O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, _)))))))))))))))))))=>
    make__MeasAndMobParametersCommon__ext5O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18
  end.
Lemma MeasAndMobParametersCommon__ext5O__F1F2_cond (z : MeasAndMobParametersCommon__ext5O__Type)
  : MeasAndMobParametersCommon__ext5O__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext5O__list (MeasAndMobParametersCommon__ext5O__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext5O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext5O__F1F2_cond2 (z : MeasAndMobParametersCommon__ext5O__Type)
 : MeasAndMobParametersCommon__ext5O__F2 (MeasAndMobParametersCommon__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext5O__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext5O__list)
  : seq_cond MeasAndMobParametersCommon__ext5O__list y ->
 (MeasAndMobParametersCommon__ext5O__cond (MeasAndMobParametersCommon__ext5O__F2 y)) /\  MeasAndMobParametersCommon__ext5O__F1 (MeasAndMobParametersCommon__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext5O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext5O__Format : T_Format MeasAndMobParametersCommon__ext5O__Type MeasAndMobParametersCommon__ext5O__cond :=
        proj2_format  MeasAndMobParametersCommon__ext5O__cond MeasAndMobParametersCommon__ext5O__list__Format
    MeasAndMobParametersCommon__ext5O__F1 MeasAndMobParametersCommon__ext5O__F2 MeasAndMobParametersCommon__ext5O__F1F2_cond  MeasAndMobParametersCommon__ext5O__F1F2_cond2 MeasAndMobParametersCommon__ext5O__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext5O__cond MeasAndMobParametersCommon__ext5O__Format.

Definition MeasAndMobParametersCommon__ext5__check_all_none (b : MeasAndMobParametersCommon__ext5O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersCommon__ext5O__Type None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersCommon__ext5__Format : T_Format MeasAndMobParametersCommon__ext5__Type MeasAndMobParametersCommon__ext5__cond :=
  restrict_add_format MeasAndMobParametersCommon__ext5__check_all_none MeasAndMobParametersCommon__ext5O__Format.

Opaque MeasAndMobParametersCommon__ext5__cond MeasAndMobParametersCommon__ext5__Format.

Definition MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Format : T_Format MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__nat__Format MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F1 MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F2 MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F1F2 MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__cond MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Format.

Definition MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Format : T_Format MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__nat__Format MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F1 MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F2 MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F1F2 MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__cond MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Format.

Definition MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Format : T_Format MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__nat__Format MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F1 MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F2 MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F1F2 MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__cond MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Format.

Definition MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Format : T_Format MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__nat__Format MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F1 MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F2 MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F1F2 MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__cond MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Format.


Definition MeasAndMobParametersCommon__ext6O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext6O__list.
Definition MeasAndMobParametersCommon__ext6O__Format_list : MeasAndMobParametersCommon__ext6O__Format_Type :=
  (MeasAndMobParametersCommon__ext6O__parallelSMTC_r17__Format, (MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17__Format, (MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17__Format, (MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17__Format, unit_format)))).
Definition MeasAndMobParametersCommon__ext6O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext6O__list MeasAndMobParametersCommon__ext6O__Format_list.
Definition MeasAndMobParametersCommon__ext6O__F1 z :=
  (MeasAndMobParametersCommon__ext6O__parallelSMTC_r17 z, (MeasAndMobParametersCommon__ext6O__concurrentMeasGapEUTRA_r17 z, (MeasAndMobParametersCommon__ext6O__serviceLinkPropDelayDiffReporting_r17 z, (MeasAndMobParametersCommon__ext6O__ncsg_SymbolLevelScheduleRestrictionInter_r17 z, tt)))).
Definition MeasAndMobParametersCommon__ext6O__F2 (y : seq_type MeasAndMobParametersCommon__ext6O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasAndMobParametersCommon__ext6O__Type i0 i1 i2 i3
  end.
Lemma MeasAndMobParametersCommon__ext6O__F1F2_cond (z : MeasAndMobParametersCommon__ext6O__Type)
  : MeasAndMobParametersCommon__ext6O__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext6O__list (MeasAndMobParametersCommon__ext6O__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext6O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext6O__F1F2_cond2 (z : MeasAndMobParametersCommon__ext6O__Type)
 : MeasAndMobParametersCommon__ext6O__F2 (MeasAndMobParametersCommon__ext6O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext6O__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext6O__list)
  : seq_cond MeasAndMobParametersCommon__ext6O__list y ->
 (MeasAndMobParametersCommon__ext6O__cond (MeasAndMobParametersCommon__ext6O__F2 y)) /\  MeasAndMobParametersCommon__ext6O__F1 (MeasAndMobParametersCommon__ext6O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext6O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext6O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext6O__Format : T_Format MeasAndMobParametersCommon__ext6O__Type MeasAndMobParametersCommon__ext6O__cond :=
        proj2_format  MeasAndMobParametersCommon__ext6O__cond MeasAndMobParametersCommon__ext6O__list__Format
    MeasAndMobParametersCommon__ext6O__F1 MeasAndMobParametersCommon__ext6O__F2 MeasAndMobParametersCommon__ext6O__F1F2_cond  MeasAndMobParametersCommon__ext6O__F1F2_cond2 MeasAndMobParametersCommon__ext6O__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext6O__cond MeasAndMobParametersCommon__ext6O__Format.

Definition MeasAndMobParametersCommon__ext6__check_all_none (b : MeasAndMobParametersCommon__ext6O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersCommon__ext6O__Type None None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersCommon__ext6__Format : T_Format MeasAndMobParametersCommon__ext6__Type MeasAndMobParametersCommon__ext6__cond :=
  restrict_add_format MeasAndMobParametersCommon__ext6__check_all_none MeasAndMobParametersCommon__ext6O__Format.

Opaque MeasAndMobParametersCommon__ext6__cond MeasAndMobParametersCommon__ext6__Format.

Definition MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Format : T_Format MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__nat__Format MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F1 MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F2 MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F1F2 MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__F2F1.

Opaque MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__cond MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Format.

Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__Format : T_Format Z MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__cond :=
 ranged_int_format (1) (32) MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__helper1 MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__helper2.

Opaque MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__Format.

Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__Format : T_Format Z MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__cond :=
 ranged_int_format (1) (32) MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__helper1 MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__helper2.

Opaque MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__Format.

Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__Format : T_Format Z MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__cond :=
 ranged_int_format (1) (32) MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__helper1 MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__helper2.

Opaque MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__Format.


Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Format_list : MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Format_Type :=
  (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17__Format, (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17__Format, (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17__Format, unit_format))).
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Format_list.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1 z :=
  (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_Only_r17 z, (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr2_Only_r17 z, (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__fr1_AndFR2_r17 z, tt))).
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F2 (y : seq_type MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Type i0 i1 i2
  end.
Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1F2_cond (z : MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Type)
  : MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1F2_cond2 (z : MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Type)
 : MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F2 (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list)
  : seq_cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list y ->
 (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F2 y)) /\  MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1 (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Format : T_Format MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Type MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond :=
        proj2_format  MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__list__Format
    MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1 MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F2 MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1F2_cond  MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F1F2_cond2 MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__cond MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Format.


Definition MeasAndMobParametersCommon__ext7O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__ext7O__list.
Definition MeasAndMobParametersCommon__ext7O__Format_list : MeasAndMobParametersCommon__ext7O__Format_Type :=
  (MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17__Format, (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17__Format, unit_format)).
Definition MeasAndMobParametersCommon__ext7O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersCommon__ext7O__list MeasAndMobParametersCommon__ext7O__Format_list.
Definition MeasAndMobParametersCommon__ext7O__F1 z :=
  (MeasAndMobParametersCommon__ext7O__eventD1_MeasReportTrigger_r17 z, (MeasAndMobParametersCommon__ext7O__independentGapConfig_maxCC_r17 z, tt)).
Definition MeasAndMobParametersCommon__ext7O__F2 (y : seq_type MeasAndMobParametersCommon__ext7O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasAndMobParametersCommon__ext7O__Type i0 i1
  end.
Lemma MeasAndMobParametersCommon__ext7O__F1F2_cond (z : MeasAndMobParametersCommon__ext7O__Type)
  : MeasAndMobParametersCommon__ext7O__cond z ->
  (seq_cond MeasAndMobParametersCommon__ext7O__list (MeasAndMobParametersCommon__ext7O__F1 z)).
intro H. unfold MeasAndMobParametersCommon__ext7O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext7O__F1F2_cond2 (z : MeasAndMobParametersCommon__ext7O__Type)
 : MeasAndMobParametersCommon__ext7O__F2 (MeasAndMobParametersCommon__ext7O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersCommon__ext7O__F2F1_cond (y : seq_type MeasAndMobParametersCommon__ext7O__list)
  : seq_cond MeasAndMobParametersCommon__ext7O__list y ->
 (MeasAndMobParametersCommon__ext7O__cond (MeasAndMobParametersCommon__ext7O__F2 y)) /\  MeasAndMobParametersCommon__ext7O__F1 (MeasAndMobParametersCommon__ext7O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersCommon__ext7O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersCommon__ext7O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersCommon__ext7O__Format : T_Format MeasAndMobParametersCommon__ext7O__Type MeasAndMobParametersCommon__ext7O__cond :=
        proj2_format  MeasAndMobParametersCommon__ext7O__cond MeasAndMobParametersCommon__ext7O__list__Format
    MeasAndMobParametersCommon__ext7O__F1 MeasAndMobParametersCommon__ext7O__F2 MeasAndMobParametersCommon__ext7O__F1F2_cond  MeasAndMobParametersCommon__ext7O__F1F2_cond2 MeasAndMobParametersCommon__ext7O__F2F1_cond.
Opaque MeasAndMobParametersCommon__ext7O__cond MeasAndMobParametersCommon__ext7O__Format.

Definition MeasAndMobParametersCommon__ext7__check_all_none (b : MeasAndMobParametersCommon__ext7O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersCommon__ext7O__Type None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersCommon__ext7__Format : T_Format MeasAndMobParametersCommon__ext7__Type MeasAndMobParametersCommon__ext7__cond :=
  restrict_add_format MeasAndMobParametersCommon__ext7__check_all_none MeasAndMobParametersCommon__ext7O__Format.

Opaque MeasAndMobParametersCommon__ext7__cond MeasAndMobParametersCommon__ext7__Format.


Definition MeasAndMobParametersCommon__root_Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersCommon__root_list.
Definition MeasAndMobParametersCommon__root_Format_list : MeasAndMobParametersCommon__root_Format_Type :=
  (MeasAndMobParametersCommon__supportedGapPattern__Format, (MeasAndMobParametersCommon__ssb_RLM__Format, (MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM__Format, unit_format))).

Definition MeasAndMobParametersCommon__ext_Format_Type := Eval cbn in get_formats MeasAndMobParametersCommon__ext_list.
Definition MeasAndMobParametersCommon__ext_Format_list : MeasAndMobParametersCommon__ext_Format_Type :=
  (MeasAndMobParametersCommon__ext0__Format, (MeasAndMobParametersCommon__ext1__Format, (MeasAndMobParametersCommon__ext2__Format, (MeasAndMobParametersCommon__ext3__Format, (MeasAndMobParametersCommon__ext4__Format, (MeasAndMobParametersCommon__ext5__Format, (MeasAndMobParametersCommon__ext6__Format, (MeasAndMobParametersCommon__ext7__Format, unit__Format)))))))).

Definition MeasAndMobParametersCommon__list_type : Set := (seq_type MeasAndMobParametersCommon__root_list) * (seq_ext_type MeasAndMobParametersCommon__ext_list).
Definition MeasAndMobParametersCommon__list_cond (z : MeasAndMobParametersCommon__list_type) : Prop :=
        (seq_cond MeasAndMobParametersCommon__root_list (fst z)) /\ (seq_ext_cond MeasAndMobParametersCommon__ext_list (snd z)).
Definition MeasAndMobParametersCommon__list_format : T_Format MeasAndMobParametersCommon__list_type MeasAndMobParametersCommon__list_cond :=
 (* Eval compute in *) seq_ext_format MeasAndMobParametersCommon__root_list MeasAndMobParametersCommon__root_Format_list MeasAndMobParametersCommon__ext_list MeasAndMobParametersCommon__ext_Format_list.

Opaque MeasAndMobParametersCommon__list_format.
Definition MeasAndMobParametersCommon__F1 (z : MeasAndMobParametersCommon__Type) : MeasAndMobParametersCommon__list_type :=
  (((MeasAndMobParametersCommon__supportedGapPattern z, (MeasAndMobParametersCommon__ssb_RLM z, (MeasAndMobParametersCommon__ssb_AndCSI_RS_RLM z, tt)))), (
(MeasAndMobParametersCommon__ext0 z, (MeasAndMobParametersCommon__ext1 z, (MeasAndMobParametersCommon__ext2 z, (MeasAndMobParametersCommon__ext3 z, (MeasAndMobParametersCommon__ext4 z, (MeasAndMobParametersCommon__ext5 z, (MeasAndMobParametersCommon__ext6 z, (MeasAndMobParametersCommon__ext7 z, tt)))))))))).
Definition MeasAndMobParametersCommon__F2 (y : MeasAndMobParametersCommon__list_type) : MeasAndMobParametersCommon__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _)))))))))=>
    make__MeasAndMobParametersCommon__Type j0 j1 j2 i0 i1 i2 i3 i4 i5 i6 i7
  end.
Definition MeasAndMobParametersCommon__helper1 : (forall a : MeasAndMobParametersCommon__Type, MeasAndMobParametersCommon__cond a -> MeasAndMobParametersCommon__list_cond (MeasAndMobParametersCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasAndMobParametersCommon__helper2 : (forall a : MeasAndMobParametersCommon__Type, MeasAndMobParametersCommon__F2 (MeasAndMobParametersCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasAndMobParametersCommon__helper3 : (forall b : MeasAndMobParametersCommon__list_type, MeasAndMobParametersCommon__list_cond b -> MeasAndMobParametersCommon__cond (MeasAndMobParametersCommon__F2 b) /\ MeasAndMobParametersCommon__F1 (MeasAndMobParametersCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasAndMobParametersCommon__cond, MeasAndMobParametersCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasAndMobParametersCommon__Format : T_Format MeasAndMobParametersCommon__Type MeasAndMobParametersCommon__cond :=
 proj2_format MeasAndMobParametersCommon__cond MeasAndMobParametersCommon__list_format  MeasAndMobParametersCommon__F1 MeasAndMobParametersCommon__F2 MeasAndMobParametersCommon__helper1 MeasAndMobParametersCommon__helper2 MeasAndMobParametersCommon__helper3.

Opaque MeasAndMobParametersCommon__cond MeasAndMobParametersCommon__Format.

