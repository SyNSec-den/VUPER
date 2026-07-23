Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Type : Set :=
 | MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__supported
.
Definition MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__cond := (fun (_ : MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Type) => True).
Lemma MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__nat__helper.

Definition MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F1 t :=
  match t with
  | MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__supported => 0
  end.
Definition MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F2 n :=
  match n with
  | 0 => MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__supported
  | _ => MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__supported
  end.
Lemma MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F1F2 : forall x : MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Type, (MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F1 x <= 0) /\ MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F2 (MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F1 (MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Type : Set :=
 | MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__supported
.
Definition MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__cond := (fun (_ : MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Type) => True).
Lemma MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__nat__helper.

Definition MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F1 t :=
  match t with
  | MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__supported => 0
  end.
Definition MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F2 n :=
  match n with
  | 0 => MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__supported
  | _ => MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__supported
  end.
Lemma MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F1F2 : forall x : MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Type, (MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F1 x <= 0) /\ MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F2 (MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F1 (MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Type : Set :=
 | MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__supported
.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__cond := (fun (_ : MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Type) => True).
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__nat__helper.

Definition MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F1 t :=
  match t with
  | MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__supported => 0
  end.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F2 n :=
  match n with
  | 0 => MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__supported
  | _ => MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__supported
  end.
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F1F2 : forall x : MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Type, (MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F1 x <= 0) /\ MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F2 (MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F1 (MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Type : Set :=
 | MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__supported
.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__cond := (fun (_ : MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Type) => True).
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__nat__helper.

Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F1 t :=
  match t with
  | MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__supported => 0
  end.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__supported
  | _ => MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__supported
  end.
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F1F2 : forall x : MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Type, (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F1 x <= 0) /\ MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F2 (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F1 (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Type : Set :=
 | MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__supported
.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__cond := (fun (_ : MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Type) => True).
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__nat__helper.

Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F1 t :=
  match t with
  | MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__supported => 0
  end.
Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__supported
  | _ => MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__supported
  end.
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F1F2 : forall x : MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Type, (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F1 x <= 0) /\ MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F2 (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F1 (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersXDD_Diff__ext0O__Type : Set :=
  make__MeasAndMobParametersXDD_Diff__ext0O__Type {
    MeasAndMobParametersXDD_Diff__ext0O__handoverInterF : option MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Type ;
    MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC : option MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Type ;
    MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC : option MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Type ;
}.
Definition MeasAndMobParametersXDD_Diff__ext0O__list := (
 Opt MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Type MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__cond ::
 Opt MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Type MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__cond ::
 Opt MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Type MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__cond ::
 nil).
Definition MeasAndMobParametersXDD_Diff__ext0O__cond z := 
  opt_cond MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__cond (MeasAndMobParametersXDD_Diff__ext0O__handoverInterF z) /\
  opt_cond MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__cond (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC z) /\
  opt_cond MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__cond (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC z) /\
  True.

Definition MeasAndMobParametersXDD_Diff__ext0__Type := MeasAndMobParametersXDD_Diff__ext0O__Type.
Definition MeasAndMobParametersXDD_Diff__ext0__cond := MeasAndMobParametersXDD_Diff__ext0O__cond.

Inductive MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Type : Set :=
 | MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__supported
.
Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__cond := (fun (_ : MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Type) => True).
Lemma MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__nat__helper.

Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F1 t :=
  match t with
  | MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__supported => 0
  end.
Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F2 n :=
  match n with
  | 0 => MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__supported
  | _ => MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__supported
  end.
Lemma MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F1F2 : forall x : MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Type, (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F1 x <= 0) /\ MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F2 (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F1 (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Type : Set :=
 | MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__supported
.
Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__cond := (fun (_ : MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Type) => True).
Lemma MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__nat__helper.

Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F1 t :=
  match t with
  | MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__supported => 0
  end.
Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F2 n :=
  match n with
  | 0 => MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__supported
  | _ => MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__supported
  end.
Lemma MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F1F2 : forall x : MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Type, (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F1 x <= 0) /\ MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F2 (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F1 (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersXDD_Diff__ext1O__Type : Set :=
  make__MeasAndMobParametersXDD_Diff__ext1O__Type {
    MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh : option MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Type ;
    MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX : option MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Type ;
}.
Definition MeasAndMobParametersXDD_Diff__ext1O__list := (
 Opt MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Type MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__cond ::
 Opt MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Type MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__cond ::
 nil).
Definition MeasAndMobParametersXDD_Diff__ext1O__cond z := 
  opt_cond MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__cond (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh z) /\
  opt_cond MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__cond (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX z) /\
  True.

Definition MeasAndMobParametersXDD_Diff__ext1__Type := MeasAndMobParametersXDD_Diff__ext1O__Type.
Definition MeasAndMobParametersXDD_Diff__ext1__cond := MeasAndMobParametersXDD_Diff__ext1O__cond.

Inductive MeasAndMobParametersXDD_Diff__ext2O__dummy__Type : Set :=
 | MeasAndMobParametersXDD_Diff__ext2O__dummy__supported
.
Definition MeasAndMobParametersXDD_Diff__ext2O__dummy__cond := (fun (_ : MeasAndMobParametersXDD_Diff__ext2O__dummy__Type) => True).
Lemma MeasAndMobParametersXDD_Diff__ext2O__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersXDD_Diff__ext2O__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersXDD_Diff__ext2O__dummy__nat__helper.

Definition MeasAndMobParametersXDD_Diff__ext2O__dummy__F1 t :=
  match t with
  | MeasAndMobParametersXDD_Diff__ext2O__dummy__supported => 0
  end.
Definition MeasAndMobParametersXDD_Diff__ext2O__dummy__F2 n :=
  match n with
  | 0 => MeasAndMobParametersXDD_Diff__ext2O__dummy__supported
  | _ => MeasAndMobParametersXDD_Diff__ext2O__dummy__supported
  end.
Lemma MeasAndMobParametersXDD_Diff__ext2O__dummy__F1F2 : forall x : MeasAndMobParametersXDD_Diff__ext2O__dummy__Type, (MeasAndMobParametersXDD_Diff__ext2O__dummy__F1 x <= 0) /\ MeasAndMobParametersXDD_Diff__ext2O__dummy__F2 (MeasAndMobParametersXDD_Diff__ext2O__dummy__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext2O__dummy__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersXDD_Diff__ext2O__dummy__F1 (MeasAndMobParametersXDD_Diff__ext2O__dummy__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersXDD_Diff__ext2O__Type : Set :=
  make__MeasAndMobParametersXDD_Diff__ext2O__Type {
    MeasAndMobParametersXDD_Diff__ext2O__dummy : option MeasAndMobParametersXDD_Diff__ext2O__dummy__Type ;
}.
Definition MeasAndMobParametersXDD_Diff__ext2O__list := (
 Opt MeasAndMobParametersXDD_Diff__ext2O__dummy__Type MeasAndMobParametersXDD_Diff__ext2O__dummy__cond ::
 nil).
Definition MeasAndMobParametersXDD_Diff__ext2O__cond z := 
  opt_cond MeasAndMobParametersXDD_Diff__ext2O__dummy__cond (MeasAndMobParametersXDD_Diff__ext2O__dummy z) /\
  True.

Definition MeasAndMobParametersXDD_Diff__ext2__Type := MeasAndMobParametersXDD_Diff__ext2O__Type.
Definition MeasAndMobParametersXDD_Diff__ext2__cond := MeasAndMobParametersXDD_Diff__ext2O__cond.

Record MeasAndMobParametersXDD_Diff__Type : Set :=
  make__MeasAndMobParametersXDD_Diff__Type {
    MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport : option MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Type ;
    MeasAndMobParametersXDD_Diff__eventA_MeasAndReport : option MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Type ;
    MeasAndMobParametersXDD_Diff__ext0 : option MeasAndMobParametersXDD_Diff__ext0__Type ;
    MeasAndMobParametersXDD_Diff__ext1 : option MeasAndMobParametersXDD_Diff__ext1__Type ;
    MeasAndMobParametersXDD_Diff__ext2 : option MeasAndMobParametersXDD_Diff__ext2__Type ;
}.
Definition MeasAndMobParametersXDD_Diff__root_list : list seq_elem := (
 Opt MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Type MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__cond ::
 Opt MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Type MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__cond ::
 nil).
Definition MeasAndMobParametersXDD_Diff__ext_list : list typ := (
  typ_cons MeasAndMobParametersXDD_Diff__ext0__Type MeasAndMobParametersXDD_Diff__ext0__cond ::
  typ_cons MeasAndMobParametersXDD_Diff__ext1__Type MeasAndMobParametersXDD_Diff__ext1__cond ::
  typ_cons MeasAndMobParametersXDD_Diff__ext2__Type MeasAndMobParametersXDD_Diff__ext2__cond ::
  nil).
Definition MeasAndMobParametersXDD_Diff__cond (z : MeasAndMobParametersXDD_Diff__Type) := 
(  opt_cond MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__cond (MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport z) /\
  opt_cond MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__cond (MeasAndMobParametersXDD_Diff__eventA_MeasAndReport z) /\
  True) /\ 
(  opt_cond MeasAndMobParametersXDD_Diff__ext0__cond (MeasAndMobParametersXDD_Diff__ext0 z) /\
  opt_cond MeasAndMobParametersXDD_Diff__ext1__cond (MeasAndMobParametersXDD_Diff__ext1 z) /\
  opt_cond MeasAndMobParametersXDD_Diff__ext2__cond (MeasAndMobParametersXDD_Diff__ext2 z) /\
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
Definition MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Format : T_Format MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__nat__Format MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F1 MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F2 MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F1F2 MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__F2F1.

Opaque MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__cond MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Format.

Definition MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Format : T_Format MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__nat__Format MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F1 MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F2 MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F1F2 MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__F2F1.

Opaque MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__cond MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Format.

Definition MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Format : T_Format MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__nat__Format MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F1 MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F2 MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F1F2 MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__F2F1.

Opaque MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__cond MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Format.

Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Format : T_Format MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__nat__Format MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F1 MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F2 MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F1F2 MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__F2F1.

Opaque MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__cond MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Format.

Definition MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Format : T_Format MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__nat__Format MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F1 MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F2 MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F1F2 MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__F2F1.

Opaque MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__cond MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Format.


Definition MeasAndMobParametersXDD_Diff__ext0O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersXDD_Diff__ext0O__list.
Definition MeasAndMobParametersXDD_Diff__ext0O__Format_list : MeasAndMobParametersXDD_Diff__ext0O__Format_Type :=
  (MeasAndMobParametersXDD_Diff__ext0O__handoverInterF__Format, (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC__Format, (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC__Format, unit_format))).
Definition MeasAndMobParametersXDD_Diff__ext0O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersXDD_Diff__ext0O__list MeasAndMobParametersXDD_Diff__ext0O__Format_list.
Definition MeasAndMobParametersXDD_Diff__ext0O__F1 z :=
  (MeasAndMobParametersXDD_Diff__ext0O__handoverInterF z, (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_EPC z, (MeasAndMobParametersXDD_Diff__ext0O__handoverLTE_5GC z, tt))).
Definition MeasAndMobParametersXDD_Diff__ext0O__F2 (y : seq_type MeasAndMobParametersXDD_Diff__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasAndMobParametersXDD_Diff__ext0O__Type i0 i1 i2
  end.
Lemma MeasAndMobParametersXDD_Diff__ext0O__F1F2_cond (z : MeasAndMobParametersXDD_Diff__ext0O__Type)
  : MeasAndMobParametersXDD_Diff__ext0O__cond z ->
  (seq_cond MeasAndMobParametersXDD_Diff__ext0O__list (MeasAndMobParametersXDD_Diff__ext0O__F1 z)).
intro H. unfold MeasAndMobParametersXDD_Diff__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext0O__F1F2_cond2 (z : MeasAndMobParametersXDD_Diff__ext0O__Type)
 : MeasAndMobParametersXDD_Diff__ext0O__F2 (MeasAndMobParametersXDD_Diff__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext0O__F2F1_cond (y : seq_type MeasAndMobParametersXDD_Diff__ext0O__list)
  : seq_cond MeasAndMobParametersXDD_Diff__ext0O__list y ->
 (MeasAndMobParametersXDD_Diff__ext0O__cond (MeasAndMobParametersXDD_Diff__ext0O__F2 y)) /\  MeasAndMobParametersXDD_Diff__ext0O__F1 (MeasAndMobParametersXDD_Diff__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersXDD_Diff__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersXDD_Diff__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersXDD_Diff__ext0O__Format : T_Format MeasAndMobParametersXDD_Diff__ext0O__Type MeasAndMobParametersXDD_Diff__ext0O__cond :=
        proj2_format  MeasAndMobParametersXDD_Diff__ext0O__cond MeasAndMobParametersXDD_Diff__ext0O__list__Format
    MeasAndMobParametersXDD_Diff__ext0O__F1 MeasAndMobParametersXDD_Diff__ext0O__F2 MeasAndMobParametersXDD_Diff__ext0O__F1F2_cond  MeasAndMobParametersXDD_Diff__ext0O__F1F2_cond2 MeasAndMobParametersXDD_Diff__ext0O__F2F1_cond.
Opaque MeasAndMobParametersXDD_Diff__ext0O__cond MeasAndMobParametersXDD_Diff__ext0O__Format.

Definition MeasAndMobParametersXDD_Diff__ext0__check_all_none (b : MeasAndMobParametersXDD_Diff__ext0O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersXDD_Diff__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersXDD_Diff__ext0__Format : T_Format MeasAndMobParametersXDD_Diff__ext0__Type MeasAndMobParametersXDD_Diff__ext0__cond :=
  restrict_add_format MeasAndMobParametersXDD_Diff__ext0__check_all_none MeasAndMobParametersXDD_Diff__ext0O__Format.

Opaque MeasAndMobParametersXDD_Diff__ext0__cond MeasAndMobParametersXDD_Diff__ext0__Format.

Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Format : T_Format MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__nat__Format MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F1 MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F2 MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F1F2 MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__F2F1.

Opaque MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__cond MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Format.

Definition MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Format : T_Format MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__nat__Format MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F1 MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F2 MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F1F2 MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__F2F1.

Opaque MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__cond MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Format.


Definition MeasAndMobParametersXDD_Diff__ext1O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersXDD_Diff__ext1O__list.
Definition MeasAndMobParametersXDD_Diff__ext1O__Format_list : MeasAndMobParametersXDD_Diff__ext1O__Format_Type :=
  (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh__Format, (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX__Format, unit_format)).
Definition MeasAndMobParametersXDD_Diff__ext1O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersXDD_Diff__ext1O__list MeasAndMobParametersXDD_Diff__ext1O__Format_list.
Definition MeasAndMobParametersXDD_Diff__ext1O__F1 z :=
  (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh z, (MeasAndMobParametersXDD_Diff__ext1O__sftd_MeasNR_Neigh_DRX z, tt)).
Definition MeasAndMobParametersXDD_Diff__ext1O__F2 (y : seq_type MeasAndMobParametersXDD_Diff__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasAndMobParametersXDD_Diff__ext1O__Type i0 i1
  end.
Lemma MeasAndMobParametersXDD_Diff__ext1O__F1F2_cond (z : MeasAndMobParametersXDD_Diff__ext1O__Type)
  : MeasAndMobParametersXDD_Diff__ext1O__cond z ->
  (seq_cond MeasAndMobParametersXDD_Diff__ext1O__list (MeasAndMobParametersXDD_Diff__ext1O__F1 z)).
intro H. unfold MeasAndMobParametersXDD_Diff__ext1O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext1O__F1F2_cond2 (z : MeasAndMobParametersXDD_Diff__ext1O__Type)
 : MeasAndMobParametersXDD_Diff__ext1O__F2 (MeasAndMobParametersXDD_Diff__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext1O__F2F1_cond (y : seq_type MeasAndMobParametersXDD_Diff__ext1O__list)
  : seq_cond MeasAndMobParametersXDD_Diff__ext1O__list y ->
 (MeasAndMobParametersXDD_Diff__ext1O__cond (MeasAndMobParametersXDD_Diff__ext1O__F2 y)) /\  MeasAndMobParametersXDD_Diff__ext1O__F1 (MeasAndMobParametersXDD_Diff__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersXDD_Diff__ext1O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersXDD_Diff__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersXDD_Diff__ext1O__Format : T_Format MeasAndMobParametersXDD_Diff__ext1O__Type MeasAndMobParametersXDD_Diff__ext1O__cond :=
        proj2_format  MeasAndMobParametersXDD_Diff__ext1O__cond MeasAndMobParametersXDD_Diff__ext1O__list__Format
    MeasAndMobParametersXDD_Diff__ext1O__F1 MeasAndMobParametersXDD_Diff__ext1O__F2 MeasAndMobParametersXDD_Diff__ext1O__F1F2_cond  MeasAndMobParametersXDD_Diff__ext1O__F1F2_cond2 MeasAndMobParametersXDD_Diff__ext1O__F2F1_cond.
Opaque MeasAndMobParametersXDD_Diff__ext1O__cond MeasAndMobParametersXDD_Diff__ext1O__Format.

Definition MeasAndMobParametersXDD_Diff__ext1__check_all_none (b : MeasAndMobParametersXDD_Diff__ext1O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersXDD_Diff__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersXDD_Diff__ext1__Format : T_Format MeasAndMobParametersXDD_Diff__ext1__Type MeasAndMobParametersXDD_Diff__ext1__cond :=
  restrict_add_format MeasAndMobParametersXDD_Diff__ext1__check_all_none MeasAndMobParametersXDD_Diff__ext1O__Format.

Opaque MeasAndMobParametersXDD_Diff__ext1__cond MeasAndMobParametersXDD_Diff__ext1__Format.

Definition MeasAndMobParametersXDD_Diff__ext2O__dummy__Format : T_Format MeasAndMobParametersXDD_Diff__ext2O__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersXDD_Diff__ext2O__dummy__nat__Format MeasAndMobParametersXDD_Diff__ext2O__dummy__F1 MeasAndMobParametersXDD_Diff__ext2O__dummy__F2 MeasAndMobParametersXDD_Diff__ext2O__dummy__F1F2 MeasAndMobParametersXDD_Diff__ext2O__dummy__F2F1.

Opaque MeasAndMobParametersXDD_Diff__ext2O__dummy__cond MeasAndMobParametersXDD_Diff__ext2O__dummy__Format.


Definition MeasAndMobParametersXDD_Diff__ext2O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersXDD_Diff__ext2O__list.
Definition MeasAndMobParametersXDD_Diff__ext2O__Format_list : MeasAndMobParametersXDD_Diff__ext2O__Format_Type :=
  (MeasAndMobParametersXDD_Diff__ext2O__dummy__Format, unit_format).
Definition MeasAndMobParametersXDD_Diff__ext2O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersXDD_Diff__ext2O__list MeasAndMobParametersXDD_Diff__ext2O__Format_list.
Definition MeasAndMobParametersXDD_Diff__ext2O__F1 z :=
  (MeasAndMobParametersXDD_Diff__ext2O__dummy z, tt).
Definition MeasAndMobParametersXDD_Diff__ext2O__F2 (y : seq_type MeasAndMobParametersXDD_Diff__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__MeasAndMobParametersXDD_Diff__ext2O__Type i0
  end.
Lemma MeasAndMobParametersXDD_Diff__ext2O__F1F2_cond (z : MeasAndMobParametersXDD_Diff__ext2O__Type)
  : MeasAndMobParametersXDD_Diff__ext2O__cond z ->
  (seq_cond MeasAndMobParametersXDD_Diff__ext2O__list (MeasAndMobParametersXDD_Diff__ext2O__F1 z)).
intro H. unfold MeasAndMobParametersXDD_Diff__ext2O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext2O__F1F2_cond2 (z : MeasAndMobParametersXDD_Diff__ext2O__Type)
 : MeasAndMobParametersXDD_Diff__ext2O__F2 (MeasAndMobParametersXDD_Diff__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersXDD_Diff__ext2O__F2F1_cond (y : seq_type MeasAndMobParametersXDD_Diff__ext2O__list)
  : seq_cond MeasAndMobParametersXDD_Diff__ext2O__list y ->
 (MeasAndMobParametersXDD_Diff__ext2O__cond (MeasAndMobParametersXDD_Diff__ext2O__F2 y)) /\  MeasAndMobParametersXDD_Diff__ext2O__F1 (MeasAndMobParametersXDD_Diff__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersXDD_Diff__ext2O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersXDD_Diff__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersXDD_Diff__ext2O__Format : T_Format MeasAndMobParametersXDD_Diff__ext2O__Type MeasAndMobParametersXDD_Diff__ext2O__cond :=
        proj2_format  MeasAndMobParametersXDD_Diff__ext2O__cond MeasAndMobParametersXDD_Diff__ext2O__list__Format
    MeasAndMobParametersXDD_Diff__ext2O__F1 MeasAndMobParametersXDD_Diff__ext2O__F2 MeasAndMobParametersXDD_Diff__ext2O__F1F2_cond  MeasAndMobParametersXDD_Diff__ext2O__F1F2_cond2 MeasAndMobParametersXDD_Diff__ext2O__F2F1_cond.
Opaque MeasAndMobParametersXDD_Diff__ext2O__cond MeasAndMobParametersXDD_Diff__ext2O__Format.

Definition MeasAndMobParametersXDD_Diff__ext2__check_all_none (b : MeasAndMobParametersXDD_Diff__ext2O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersXDD_Diff__ext2O__Type None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersXDD_Diff__ext2__Format : T_Format MeasAndMobParametersXDD_Diff__ext2__Type MeasAndMobParametersXDD_Diff__ext2__cond :=
  restrict_add_format MeasAndMobParametersXDD_Diff__ext2__check_all_none MeasAndMobParametersXDD_Diff__ext2O__Format.

Opaque MeasAndMobParametersXDD_Diff__ext2__cond MeasAndMobParametersXDD_Diff__ext2__Format.


Definition MeasAndMobParametersXDD_Diff__root_Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersXDD_Diff__root_list.
Definition MeasAndMobParametersXDD_Diff__root_Format_list : MeasAndMobParametersXDD_Diff__root_Format_Type :=
  (MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport__Format, (MeasAndMobParametersXDD_Diff__eventA_MeasAndReport__Format, unit_format)).

Definition MeasAndMobParametersXDD_Diff__ext_Format_Type := Eval cbn in get_formats MeasAndMobParametersXDD_Diff__ext_list.
Definition MeasAndMobParametersXDD_Diff__ext_Format_list : MeasAndMobParametersXDD_Diff__ext_Format_Type :=
  (MeasAndMobParametersXDD_Diff__ext0__Format, (MeasAndMobParametersXDD_Diff__ext1__Format, (MeasAndMobParametersXDD_Diff__ext2__Format, unit__Format))).

Definition MeasAndMobParametersXDD_Diff__list_type : Set := (seq_type MeasAndMobParametersXDD_Diff__root_list) * (seq_ext_type MeasAndMobParametersXDD_Diff__ext_list).
Definition MeasAndMobParametersXDD_Diff__list_cond (z : MeasAndMobParametersXDD_Diff__list_type) : Prop :=
        (seq_cond MeasAndMobParametersXDD_Diff__root_list (fst z)) /\ (seq_ext_cond MeasAndMobParametersXDD_Diff__ext_list (snd z)).
Definition MeasAndMobParametersXDD_Diff__list_format : T_Format MeasAndMobParametersXDD_Diff__list_type MeasAndMobParametersXDD_Diff__list_cond :=
 (* Eval compute in *) seq_ext_format MeasAndMobParametersXDD_Diff__root_list MeasAndMobParametersXDD_Diff__root_Format_list MeasAndMobParametersXDD_Diff__ext_list MeasAndMobParametersXDD_Diff__ext_Format_list.

Opaque MeasAndMobParametersXDD_Diff__list_format.
Definition MeasAndMobParametersXDD_Diff__F1 (z : MeasAndMobParametersXDD_Diff__Type) : MeasAndMobParametersXDD_Diff__list_type :=
  (((MeasAndMobParametersXDD_Diff__intraAndInterF_MeasAndReport z, (MeasAndMobParametersXDD_Diff__eventA_MeasAndReport z, tt))), (
(MeasAndMobParametersXDD_Diff__ext0 z, (MeasAndMobParametersXDD_Diff__ext1 z, (MeasAndMobParametersXDD_Diff__ext2 z, tt))))).
Definition MeasAndMobParametersXDD_Diff__F2 (y : MeasAndMobParametersXDD_Diff__list_type) : MeasAndMobParametersXDD_Diff__Type :=
  match y with
  | ((j0, (j1, _)), (i0, (i1, (i2, _))))=>
    make__MeasAndMobParametersXDD_Diff__Type j0 j1 i0 i1 i2
  end.
Definition MeasAndMobParametersXDD_Diff__helper1 : (forall a : MeasAndMobParametersXDD_Diff__Type, MeasAndMobParametersXDD_Diff__cond a -> MeasAndMobParametersXDD_Diff__list_cond (MeasAndMobParametersXDD_Diff__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasAndMobParametersXDD_Diff__helper2 : (forall a : MeasAndMobParametersXDD_Diff__Type, MeasAndMobParametersXDD_Diff__F2 (MeasAndMobParametersXDD_Diff__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasAndMobParametersXDD_Diff__helper3 : (forall b : MeasAndMobParametersXDD_Diff__list_type, MeasAndMobParametersXDD_Diff__list_cond b -> MeasAndMobParametersXDD_Diff__cond (MeasAndMobParametersXDD_Diff__F2 b) /\ MeasAndMobParametersXDD_Diff__F1 (MeasAndMobParametersXDD_Diff__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasAndMobParametersXDD_Diff__cond, MeasAndMobParametersXDD_Diff__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasAndMobParametersXDD_Diff__Format : T_Format MeasAndMobParametersXDD_Diff__Type MeasAndMobParametersXDD_Diff__cond :=
 proj2_format MeasAndMobParametersXDD_Diff__cond MeasAndMobParametersXDD_Diff__list_format  MeasAndMobParametersXDD_Diff__F1 MeasAndMobParametersXDD_Diff__F2 MeasAndMobParametersXDD_Diff__helper1 MeasAndMobParametersXDD_Diff__helper2 MeasAndMobParametersXDD_Diff__helper3.

Opaque MeasAndMobParametersXDD_Diff__cond MeasAndMobParametersXDD_Diff__Format.

