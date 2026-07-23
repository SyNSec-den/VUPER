Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ss_SINR_Meas__supported
.
Definition MeasAndMobParametersFRX_Diff__ss_SINR_Meas__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ss_SINR_Meas__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ss_SINR_Meas__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ss_SINR_Meas__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ss_SINR_Meas__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ss_SINR_Meas__supported
  | _ => MeasAndMobParametersFRX_Diff__ss_SINR_Meas__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Type, (MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F2 (MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F1 (MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Type : Set :=
 | MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__supported
.
Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__cond := (fun (_ : MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__nat__helper.

Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__supported
  | _ => MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F1F2 : forall x : MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Type, (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F2 (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F1 (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Type : Set :=
 | MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__supported
.
Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__cond := (fun (_ : MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__nat__helper.

Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__supported
  | _ => MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F1F2 : forall x : MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Type, (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F2 (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F1 (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Type : Set :=
 | MeasAndMobParametersFRX_Diff__csi_SINR_Meas__supported
.
Definition MeasAndMobParametersFRX_Diff__csi_SINR_Meas__cond := (fun (_ : MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__csi_SINR_Meas__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__csi_SINR_Meas__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__csi_SINR_Meas__nat__helper.

Definition MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__csi_SINR_Meas__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__csi_SINR_Meas__supported
  | _ => MeasAndMobParametersFRX_Diff__csi_SINR_Meas__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F1F2 : forall x : MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Type, (MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F2 (MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F1 (MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__csi_RS_RLM__Type : Set :=
 | MeasAndMobParametersFRX_Diff__csi_RS_RLM__supported
.
Definition MeasAndMobParametersFRX_Diff__csi_RS_RLM__cond := (fun (_ : MeasAndMobParametersFRX_Diff__csi_RS_RLM__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__csi_RS_RLM__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__csi_RS_RLM__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__csi_RS_RLM__nat__helper.

Definition MeasAndMobParametersFRX_Diff__csi_RS_RLM__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__csi_RS_RLM__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__csi_RS_RLM__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__csi_RS_RLM__supported
  | _ => MeasAndMobParametersFRX_Diff__csi_RS_RLM__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__csi_RS_RLM__F1F2 : forall x : MeasAndMobParametersFRX_Diff__csi_RS_RLM__Type, (MeasAndMobParametersFRX_Diff__csi_RS_RLM__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__csi_RS_RLM__F2 (MeasAndMobParametersFRX_Diff__csi_RS_RLM__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__csi_RS_RLM__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__csi_RS_RLM__F1 (MeasAndMobParametersFRX_Diff__csi_RS_RLM__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__supported
.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__supported
  | _ => MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Type, (MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F2 (MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F1 (MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__supported
.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__supported
  | _ => MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Type, (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F2 (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F1 (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__supported
.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__supported
  | _ => MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Type, (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F2 (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F1 (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersFRX_Diff__ext0O__Type : Set :=
  make__MeasAndMobParametersFRX_Diff__ext0O__Type {
    MeasAndMobParametersFRX_Diff__ext0O__handoverInterF : option MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Type ;
    MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC : option MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Type ;
    MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC : option MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Type ;
}.
Definition MeasAndMobParametersFRX_Diff__ext0O__list := (
 Opt MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Type MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Type MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Type MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__cond ::
 nil).
Definition MeasAndMobParametersFRX_Diff__ext0O__cond z := 
  opt_cond MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__cond (MeasAndMobParametersFRX_Diff__ext0O__handoverInterF z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__cond (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__cond (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC z) /\
  True.

Definition MeasAndMobParametersFRX_Diff__ext0__Type := MeasAndMobParametersFRX_Diff__ext0O__Type.
Definition MeasAndMobParametersFRX_Diff__ext0__cond := MeasAndMobParametersFRX_Diff__ext0O__cond.

Inductive MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n2
 | MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n4
 | MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n6
 | MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n8
.
Definition MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n2 => 0
  | MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n4 => 1
  | MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n6 => 2
  | MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n8 => 3
  end.
Definition MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n2
  | 1 => MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n4
  | 2 => MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n6
  | 3 => MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n8
  | _ => MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__n2
  end.
Lemma MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Type, (MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F1 x <= 3) /\ MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F2 (MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F2F1 : forall (y : nat) (H : y <= 3), MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F1 (MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersFRX_Diff__ext1O__Type : Set :=
  make__MeasAndMobParametersFRX_Diff__ext1O__Type {
    MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM : option MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Type ;
}.
Definition MeasAndMobParametersFRX_Diff__ext1O__list := (
 Opt MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Type MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__cond ::
 nil).
Definition MeasAndMobParametersFRX_Diff__ext1O__cond z := 
  opt_cond MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__cond (MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM z) /\
  True.

Definition MeasAndMobParametersFRX_Diff__ext1__Type := MeasAndMobParametersFRX_Diff__ext1O__Type.
Definition MeasAndMobParametersFRX_Diff__ext1__cond := MeasAndMobParametersFRX_Diff__ext1O__cond.

Inductive MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__supported
.
Definition MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__supported
  | _ => MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Type, (MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F2 (MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F1 (MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersFRX_Diff__ext2O__Type : Set :=
  make__MeasAndMobParametersFRX_Diff__ext2O__Type {
    MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology : option MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Type ;
}.
Definition MeasAndMobParametersFRX_Diff__ext2O__list := (
 Opt MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Type MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__cond ::
 nil).
Definition MeasAndMobParametersFRX_Diff__ext2O__cond z := 
  opt_cond MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__cond (MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology z) /\
  True.

Definition MeasAndMobParametersFRX_Diff__ext2__Type := MeasAndMobParametersFRX_Diff__ext2O__Type.
Definition MeasAndMobParametersFRX_Diff__ext2__cond := MeasAndMobParametersFRX_Diff__ext2O__cond.

Inductive MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__dummy__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__dummy__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__dummy__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__dummy__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__dummy__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__dummy__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__dummy__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__dummy__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__dummy__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__dummy__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__dummy__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__dummy__Type, (MeasAndMobParametersFRX_Diff__ext3O__dummy__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__dummy__F2 (MeasAndMobParametersFRX_Diff__ext3O__dummy__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__dummy__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__dummy__F1 (MeasAndMobParametersFRX_Diff__ext3O__dummy__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Type, (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F2 (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F1 (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersFRX_Diff__ext3O__Type : Set :=
  make__MeasAndMobParametersFRX_Diff__ext3O__Type {
    MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16 : option MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16 : option MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16 : option MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16 : option MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__dummy : option MeasAndMobParametersFRX_Diff__ext3O__dummy__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16 : option MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16 : option MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16 : option MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16 : option MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16 : option MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Type ;
    MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16 : option MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Type ;
}.
Definition MeasAndMobParametersFRX_Diff__ext3O__list := (
 Opt MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Type MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Type MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Type MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Type MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__dummy__Type MeasAndMobParametersFRX_Diff__ext3O__dummy__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Type MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Type MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Type MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Type MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Type MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__cond ::
 Opt MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Type MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__cond ::
 nil).
Definition MeasAndMobParametersFRX_Diff__ext3O__cond z := 
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__dummy__cond (MeasAndMobParametersFRX_Diff__ext3O__dummy z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__cond (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16 z) /\
  True.

Definition MeasAndMobParametersFRX_Diff__ext3__Type := MeasAndMobParametersFRX_Diff__ext3O__Type.
Definition MeasAndMobParametersFRX_Diff__ext3__cond := MeasAndMobParametersFRX_Diff__ext3O__cond.

Inductive MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Type : Set :=
 | MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__supported
.
Definition MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__cond := (fun (_ : MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Type) => True).
Lemma MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__nat__helper.

Definition MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F1 t :=
  match t with
  | MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__supported => 0
  end.
Definition MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__supported
  | _ => MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__supported
  end.
Lemma MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F1F2 : forall x : MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Type, (MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F1 x <= 0) /\ MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F2 (MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F1 (MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersFRX_Diff__ext4O__Type : Set :=
  make__MeasAndMobParametersFRX_Diff__ext4O__Type {
    MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16 : option MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Type ;
}.
Definition MeasAndMobParametersFRX_Diff__ext4O__list := (
 Opt MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Type MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__cond ::
 nil).
Definition MeasAndMobParametersFRX_Diff__ext4O__cond z := 
  opt_cond MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__cond (MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16 z) /\
  True.

Definition MeasAndMobParametersFRX_Diff__ext4__Type := MeasAndMobParametersFRX_Diff__ext4O__Type.
Definition MeasAndMobParametersFRX_Diff__ext4__cond := MeasAndMobParametersFRX_Diff__ext4O__cond.

Record MeasAndMobParametersFRX_Diff__Type : Set :=
  make__MeasAndMobParametersFRX_Diff__Type {
    MeasAndMobParametersFRX_Diff__ss_SINR_Meas : option MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Type ;
    MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB : option MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Type ;
    MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB : option MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Type ;
    MeasAndMobParametersFRX_Diff__csi_SINR_Meas : option MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Type ;
    MeasAndMobParametersFRX_Diff__csi_RS_RLM : option MeasAndMobParametersFRX_Diff__csi_RS_RLM__Type ;
    MeasAndMobParametersFRX_Diff__ext0 : option MeasAndMobParametersFRX_Diff__ext0__Type ;
    MeasAndMobParametersFRX_Diff__ext1 : option MeasAndMobParametersFRX_Diff__ext1__Type ;
    MeasAndMobParametersFRX_Diff__ext2 : option MeasAndMobParametersFRX_Diff__ext2__Type ;
    MeasAndMobParametersFRX_Diff__ext3 : option MeasAndMobParametersFRX_Diff__ext3__Type ;
    MeasAndMobParametersFRX_Diff__ext4 : option MeasAndMobParametersFRX_Diff__ext4__Type ;
}.
Definition MeasAndMobParametersFRX_Diff__root_list : list seq_elem := (
 Opt MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Type MeasAndMobParametersFRX_Diff__ss_SINR_Meas__cond ::
 Opt MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Type MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__cond ::
 Opt MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Type MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__cond ::
 Opt MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Type MeasAndMobParametersFRX_Diff__csi_SINR_Meas__cond ::
 Opt MeasAndMobParametersFRX_Diff__csi_RS_RLM__Type MeasAndMobParametersFRX_Diff__csi_RS_RLM__cond ::
 nil).
Definition MeasAndMobParametersFRX_Diff__ext_list : list typ := (
  typ_cons MeasAndMobParametersFRX_Diff__ext0__Type MeasAndMobParametersFRX_Diff__ext0__cond ::
  typ_cons MeasAndMobParametersFRX_Diff__ext1__Type MeasAndMobParametersFRX_Diff__ext1__cond ::
  typ_cons MeasAndMobParametersFRX_Diff__ext2__Type MeasAndMobParametersFRX_Diff__ext2__cond ::
  typ_cons MeasAndMobParametersFRX_Diff__ext3__Type MeasAndMobParametersFRX_Diff__ext3__cond ::
  typ_cons MeasAndMobParametersFRX_Diff__ext4__Type MeasAndMobParametersFRX_Diff__ext4__cond ::
  nil).
Definition MeasAndMobParametersFRX_Diff__cond (z : MeasAndMobParametersFRX_Diff__Type) := 
(  opt_cond MeasAndMobParametersFRX_Diff__ss_SINR_Meas__cond (MeasAndMobParametersFRX_Diff__ss_SINR_Meas z) /\
  opt_cond MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__cond (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB z) /\
  opt_cond MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__cond (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB z) /\
  opt_cond MeasAndMobParametersFRX_Diff__csi_SINR_Meas__cond (MeasAndMobParametersFRX_Diff__csi_SINR_Meas z) /\
  opt_cond MeasAndMobParametersFRX_Diff__csi_RS_RLM__cond (MeasAndMobParametersFRX_Diff__csi_RS_RLM z) /\
  True) /\ 
(  opt_cond MeasAndMobParametersFRX_Diff__ext0__cond (MeasAndMobParametersFRX_Diff__ext0 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext1__cond (MeasAndMobParametersFRX_Diff__ext1 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext2__cond (MeasAndMobParametersFRX_Diff__ext2 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext3__cond (MeasAndMobParametersFRX_Diff__ext3 z) /\
  opt_cond MeasAndMobParametersFRX_Diff__ext4__cond (MeasAndMobParametersFRX_Diff__ext4 z) /\
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
Definition MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Format : T_Format MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ss_SINR_Meas__nat__Format MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F1 MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F2 MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F1F2 MeasAndMobParametersFRX_Diff__ss_SINR_Meas__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ss_SINR_Meas__cond MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Format.

Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Format : T_Format MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__nat__Format MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F1 MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F2 MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F1F2 MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__F2F1.

Opaque MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__cond MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Format.

Definition MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Format : T_Format MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__nat__Format MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F1 MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F2 MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F1F2 MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__F2F1.

Opaque MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__cond MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Format.

Definition MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Format : T_Format MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__csi_SINR_Meas__nat__Format MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F1 MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F2 MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F1F2 MeasAndMobParametersFRX_Diff__csi_SINR_Meas__F2F1.

Opaque MeasAndMobParametersFRX_Diff__csi_SINR_Meas__cond MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Format.

Definition MeasAndMobParametersFRX_Diff__csi_RS_RLM__Format : T_Format MeasAndMobParametersFRX_Diff__csi_RS_RLM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__csi_RS_RLM__nat__Format MeasAndMobParametersFRX_Diff__csi_RS_RLM__F1 MeasAndMobParametersFRX_Diff__csi_RS_RLM__F2 MeasAndMobParametersFRX_Diff__csi_RS_RLM__F1F2 MeasAndMobParametersFRX_Diff__csi_RS_RLM__F2F1.

Opaque MeasAndMobParametersFRX_Diff__csi_RS_RLM__cond MeasAndMobParametersFRX_Diff__csi_RS_RLM__Format.

Definition MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Format : T_Format MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__nat__Format MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F1 MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F2 MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F1F2 MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__cond MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Format.

Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Format : T_Format MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__nat__Format MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F1 MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F2 MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F1F2 MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__cond MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Format.

Definition MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Format : T_Format MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__nat__Format MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F1 MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F2 MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F1F2 MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__cond MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Format.


Definition MeasAndMobParametersFRX_Diff__ext0O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersFRX_Diff__ext0O__list.
Definition MeasAndMobParametersFRX_Diff__ext0O__Format_list : MeasAndMobParametersFRX_Diff__ext0O__Format_Type :=
  (MeasAndMobParametersFRX_Diff__ext0O__handoverInterF__Format, (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC__Format, (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC__Format, unit_format))).
Definition MeasAndMobParametersFRX_Diff__ext0O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersFRX_Diff__ext0O__list MeasAndMobParametersFRX_Diff__ext0O__Format_list.
Definition MeasAndMobParametersFRX_Diff__ext0O__F1 z :=
  (MeasAndMobParametersFRX_Diff__ext0O__handoverInterF z, (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_EPC z, (MeasAndMobParametersFRX_Diff__ext0O__handoverLTE_5GC z, tt))).
Definition MeasAndMobParametersFRX_Diff__ext0O__F2 (y : seq_type MeasAndMobParametersFRX_Diff__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasAndMobParametersFRX_Diff__ext0O__Type i0 i1 i2
  end.
Lemma MeasAndMobParametersFRX_Diff__ext0O__F1F2_cond (z : MeasAndMobParametersFRX_Diff__ext0O__Type)
  : MeasAndMobParametersFRX_Diff__ext0O__cond z ->
  (seq_cond MeasAndMobParametersFRX_Diff__ext0O__list (MeasAndMobParametersFRX_Diff__ext0O__F1 z)).
intro H. unfold MeasAndMobParametersFRX_Diff__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext0O__F1F2_cond2 (z : MeasAndMobParametersFRX_Diff__ext0O__Type)
 : MeasAndMobParametersFRX_Diff__ext0O__F2 (MeasAndMobParametersFRX_Diff__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext0O__F2F1_cond (y : seq_type MeasAndMobParametersFRX_Diff__ext0O__list)
  : seq_cond MeasAndMobParametersFRX_Diff__ext0O__list y ->
 (MeasAndMobParametersFRX_Diff__ext0O__cond (MeasAndMobParametersFRX_Diff__ext0O__F2 y)) /\  MeasAndMobParametersFRX_Diff__ext0O__F1 (MeasAndMobParametersFRX_Diff__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersFRX_Diff__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersFRX_Diff__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersFRX_Diff__ext0O__Format : T_Format MeasAndMobParametersFRX_Diff__ext0O__Type MeasAndMobParametersFRX_Diff__ext0O__cond :=
        proj2_format  MeasAndMobParametersFRX_Diff__ext0O__cond MeasAndMobParametersFRX_Diff__ext0O__list__Format
    MeasAndMobParametersFRX_Diff__ext0O__F1 MeasAndMobParametersFRX_Diff__ext0O__F2 MeasAndMobParametersFRX_Diff__ext0O__F1F2_cond  MeasAndMobParametersFRX_Diff__ext0O__F1F2_cond2 MeasAndMobParametersFRX_Diff__ext0O__F2F1_cond.
Opaque MeasAndMobParametersFRX_Diff__ext0O__cond MeasAndMobParametersFRX_Diff__ext0O__Format.

Definition MeasAndMobParametersFRX_Diff__ext0__check_all_none (b : MeasAndMobParametersFRX_Diff__ext0O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersFRX_Diff__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersFRX_Diff__ext0__Format : T_Format MeasAndMobParametersFRX_Diff__ext0__Type MeasAndMobParametersFRX_Diff__ext0__cond :=
  restrict_add_format MeasAndMobParametersFRX_Diff__ext0__check_all_none MeasAndMobParametersFRX_Diff__ext0O__Format.

Opaque MeasAndMobParametersFRX_Diff__ext0__cond MeasAndMobParametersFRX_Diff__ext0__Format.

Definition MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Format : T_Format MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__nat__Format MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F1 MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F2 MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F1F2 MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__cond MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Format.


Definition MeasAndMobParametersFRX_Diff__ext1O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersFRX_Diff__ext1O__list.
Definition MeasAndMobParametersFRX_Diff__ext1O__Format_list : MeasAndMobParametersFRX_Diff__ext1O__Format_Type :=
  (MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM__Format, unit_format).
Definition MeasAndMobParametersFRX_Diff__ext1O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersFRX_Diff__ext1O__list MeasAndMobParametersFRX_Diff__ext1O__Format_list.
Definition MeasAndMobParametersFRX_Diff__ext1O__F1 z :=
  (MeasAndMobParametersFRX_Diff__ext1O__maxNumberResource_CSI_RS_RLM z, tt).
Definition MeasAndMobParametersFRX_Diff__ext1O__F2 (y : seq_type MeasAndMobParametersFRX_Diff__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__MeasAndMobParametersFRX_Diff__ext1O__Type i0
  end.
Lemma MeasAndMobParametersFRX_Diff__ext1O__F1F2_cond (z : MeasAndMobParametersFRX_Diff__ext1O__Type)
  : MeasAndMobParametersFRX_Diff__ext1O__cond z ->
  (seq_cond MeasAndMobParametersFRX_Diff__ext1O__list (MeasAndMobParametersFRX_Diff__ext1O__F1 z)).
intro H. unfold MeasAndMobParametersFRX_Diff__ext1O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext1O__F1F2_cond2 (z : MeasAndMobParametersFRX_Diff__ext1O__Type)
 : MeasAndMobParametersFRX_Diff__ext1O__F2 (MeasAndMobParametersFRX_Diff__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext1O__F2F1_cond (y : seq_type MeasAndMobParametersFRX_Diff__ext1O__list)
  : seq_cond MeasAndMobParametersFRX_Diff__ext1O__list y ->
 (MeasAndMobParametersFRX_Diff__ext1O__cond (MeasAndMobParametersFRX_Diff__ext1O__F2 y)) /\  MeasAndMobParametersFRX_Diff__ext1O__F1 (MeasAndMobParametersFRX_Diff__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersFRX_Diff__ext1O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersFRX_Diff__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersFRX_Diff__ext1O__Format : T_Format MeasAndMobParametersFRX_Diff__ext1O__Type MeasAndMobParametersFRX_Diff__ext1O__cond :=
        proj2_format  MeasAndMobParametersFRX_Diff__ext1O__cond MeasAndMobParametersFRX_Diff__ext1O__list__Format
    MeasAndMobParametersFRX_Diff__ext1O__F1 MeasAndMobParametersFRX_Diff__ext1O__F2 MeasAndMobParametersFRX_Diff__ext1O__F1F2_cond  MeasAndMobParametersFRX_Diff__ext1O__F1F2_cond2 MeasAndMobParametersFRX_Diff__ext1O__F2F1_cond.
Opaque MeasAndMobParametersFRX_Diff__ext1O__cond MeasAndMobParametersFRX_Diff__ext1O__Format.

Definition MeasAndMobParametersFRX_Diff__ext1__check_all_none (b : MeasAndMobParametersFRX_Diff__ext1O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersFRX_Diff__ext1O__Type None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersFRX_Diff__ext1__Format : T_Format MeasAndMobParametersFRX_Diff__ext1__Type MeasAndMobParametersFRX_Diff__ext1__cond :=
  restrict_add_format MeasAndMobParametersFRX_Diff__ext1__check_all_none MeasAndMobParametersFRX_Diff__ext1O__Format.

Opaque MeasAndMobParametersFRX_Diff__ext1__cond MeasAndMobParametersFRX_Diff__ext1__Format.

Definition MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Format : T_Format MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__nat__Format MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F1 MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F2 MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F1F2 MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__cond MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Format.


Definition MeasAndMobParametersFRX_Diff__ext2O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersFRX_Diff__ext2O__list.
Definition MeasAndMobParametersFRX_Diff__ext2O__Format_list : MeasAndMobParametersFRX_Diff__ext2O__Format_Type :=
  (MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology__Format, unit_format).
Definition MeasAndMobParametersFRX_Diff__ext2O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersFRX_Diff__ext2O__list MeasAndMobParametersFRX_Diff__ext2O__Format_list.
Definition MeasAndMobParametersFRX_Diff__ext2O__F1 z :=
  (MeasAndMobParametersFRX_Diff__ext2O__simultaneousRxDataSSB_DiffNumerology z, tt).
Definition MeasAndMobParametersFRX_Diff__ext2O__F2 (y : seq_type MeasAndMobParametersFRX_Diff__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__MeasAndMobParametersFRX_Diff__ext2O__Type i0
  end.
Lemma MeasAndMobParametersFRX_Diff__ext2O__F1F2_cond (z : MeasAndMobParametersFRX_Diff__ext2O__Type)
  : MeasAndMobParametersFRX_Diff__ext2O__cond z ->
  (seq_cond MeasAndMobParametersFRX_Diff__ext2O__list (MeasAndMobParametersFRX_Diff__ext2O__F1 z)).
intro H. unfold MeasAndMobParametersFRX_Diff__ext2O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext2O__F1F2_cond2 (z : MeasAndMobParametersFRX_Diff__ext2O__Type)
 : MeasAndMobParametersFRX_Diff__ext2O__F2 (MeasAndMobParametersFRX_Diff__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext2O__F2F1_cond (y : seq_type MeasAndMobParametersFRX_Diff__ext2O__list)
  : seq_cond MeasAndMobParametersFRX_Diff__ext2O__list y ->
 (MeasAndMobParametersFRX_Diff__ext2O__cond (MeasAndMobParametersFRX_Diff__ext2O__F2 y)) /\  MeasAndMobParametersFRX_Diff__ext2O__F1 (MeasAndMobParametersFRX_Diff__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersFRX_Diff__ext2O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersFRX_Diff__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersFRX_Diff__ext2O__Format : T_Format MeasAndMobParametersFRX_Diff__ext2O__Type MeasAndMobParametersFRX_Diff__ext2O__cond :=
        proj2_format  MeasAndMobParametersFRX_Diff__ext2O__cond MeasAndMobParametersFRX_Diff__ext2O__list__Format
    MeasAndMobParametersFRX_Diff__ext2O__F1 MeasAndMobParametersFRX_Diff__ext2O__F2 MeasAndMobParametersFRX_Diff__ext2O__F1F2_cond  MeasAndMobParametersFRX_Diff__ext2O__F1F2_cond2 MeasAndMobParametersFRX_Diff__ext2O__F2F1_cond.
Opaque MeasAndMobParametersFRX_Diff__ext2O__cond MeasAndMobParametersFRX_Diff__ext2O__Format.

Definition MeasAndMobParametersFRX_Diff__ext2__check_all_none (b : MeasAndMobParametersFRX_Diff__ext2O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersFRX_Diff__ext2O__Type None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersFRX_Diff__ext2__Format : T_Format MeasAndMobParametersFRX_Diff__ext2__Type MeasAndMobParametersFRX_Diff__ext2__cond :=
  restrict_add_format MeasAndMobParametersFRX_Diff__ext2__check_all_none MeasAndMobParametersFRX_Diff__ext2O__Format.

Opaque MeasAndMobParametersFRX_Diff__ext2__cond MeasAndMobParametersFRX_Diff__ext2__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__cond MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__cond MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__cond MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__cond MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__dummy__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__dummy__nat__Format MeasAndMobParametersFRX_Diff__ext3O__dummy__F1 MeasAndMobParametersFRX_Diff__ext3O__dummy__F2 MeasAndMobParametersFRX_Diff__ext3O__dummy__F1F2 MeasAndMobParametersFRX_Diff__ext3O__dummy__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__dummy__cond MeasAndMobParametersFRX_Diff__ext3O__dummy__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__cond MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__cond MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__cond MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__cond MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__cond MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Format.

Definition MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__nat__Format MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F1 MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F2 MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F1F2 MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__cond MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Format.


Definition MeasAndMobParametersFRX_Diff__ext3O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersFRX_Diff__ext3O__list.
Definition MeasAndMobParametersFRX_Diff__ext3O__Format_list : MeasAndMobParametersFRX_Diff__ext3O__Format_Type :=
  (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__dummy__Format, (MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16__Format, (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16__Format, unit_format))))))))))).
Definition MeasAndMobParametersFRX_Diff__ext3O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersFRX_Diff__ext3O__list MeasAndMobParametersFRX_Diff__ext3O__Format_list.
Definition MeasAndMobParametersFRX_Diff__ext3O__F1 z :=
  (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_ENDC_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NEDC_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__nr_AutonomousGaps_NRDC_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__dummy z, (MeasAndMobParametersFRX_Diff__ext3O__cli_RSSI_Meas_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__cli_SRS_RSRP_Meas_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__interFrequencyMeas_NoGap_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__simultaneousRxDataSSB_DiffNumerology_Inter_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasReport_r16 z, (MeasAndMobParametersFRX_Diff__ext3O__idleInactiveNR_MeasBeamReport_r16 z, tt))))))))))).
Definition MeasAndMobParametersFRX_Diff__ext3O__F2 (y : seq_type MeasAndMobParametersFRX_Diff__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, _)))))))))))=>
    make__MeasAndMobParametersFRX_Diff__ext3O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10
  end.
Lemma MeasAndMobParametersFRX_Diff__ext3O__F1F2_cond (z : MeasAndMobParametersFRX_Diff__ext3O__Type)
  : MeasAndMobParametersFRX_Diff__ext3O__cond z ->
  (seq_cond MeasAndMobParametersFRX_Diff__ext3O__list (MeasAndMobParametersFRX_Diff__ext3O__F1 z)).
intro H. unfold MeasAndMobParametersFRX_Diff__ext3O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__F1F2_cond2 (z : MeasAndMobParametersFRX_Diff__ext3O__Type)
 : MeasAndMobParametersFRX_Diff__ext3O__F2 (MeasAndMobParametersFRX_Diff__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext3O__F2F1_cond (y : seq_type MeasAndMobParametersFRX_Diff__ext3O__list)
  : seq_cond MeasAndMobParametersFRX_Diff__ext3O__list y ->
 (MeasAndMobParametersFRX_Diff__ext3O__cond (MeasAndMobParametersFRX_Diff__ext3O__F2 y)) /\  MeasAndMobParametersFRX_Diff__ext3O__F1 (MeasAndMobParametersFRX_Diff__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersFRX_Diff__ext3O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersFRX_Diff__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersFRX_Diff__ext3O__Format : T_Format MeasAndMobParametersFRX_Diff__ext3O__Type MeasAndMobParametersFRX_Diff__ext3O__cond :=
        proj2_format  MeasAndMobParametersFRX_Diff__ext3O__cond MeasAndMobParametersFRX_Diff__ext3O__list__Format
    MeasAndMobParametersFRX_Diff__ext3O__F1 MeasAndMobParametersFRX_Diff__ext3O__F2 MeasAndMobParametersFRX_Diff__ext3O__F1F2_cond  MeasAndMobParametersFRX_Diff__ext3O__F1F2_cond2 MeasAndMobParametersFRX_Diff__ext3O__F2F1_cond.
Opaque MeasAndMobParametersFRX_Diff__ext3O__cond MeasAndMobParametersFRX_Diff__ext3O__Format.

Definition MeasAndMobParametersFRX_Diff__ext3__check_all_none (b : MeasAndMobParametersFRX_Diff__ext3O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersFRX_Diff__ext3O__Type None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersFRX_Diff__ext3__Format : T_Format MeasAndMobParametersFRX_Diff__ext3__Type MeasAndMobParametersFRX_Diff__ext3__cond :=
  restrict_add_format MeasAndMobParametersFRX_Diff__ext3__check_all_none MeasAndMobParametersFRX_Diff__ext3O__Format.

Opaque MeasAndMobParametersFRX_Diff__ext3__cond MeasAndMobParametersFRX_Diff__ext3__Format.

Definition MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Format : T_Format MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__nat__Format MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F1 MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F2 MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F1F2 MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__F2F1.

Opaque MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__cond MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Format.


Definition MeasAndMobParametersFRX_Diff__ext4O__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersFRX_Diff__ext4O__list.
Definition MeasAndMobParametersFRX_Diff__ext4O__Format_list : MeasAndMobParametersFRX_Diff__ext4O__Format_Type :=
  (MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16__Format, unit_format).
Definition MeasAndMobParametersFRX_Diff__ext4O__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersFRX_Diff__ext4O__list MeasAndMobParametersFRX_Diff__ext4O__Format_list.
Definition MeasAndMobParametersFRX_Diff__ext4O__F1 z :=
  (MeasAndMobParametersFRX_Diff__ext4O__increasedNumberofCSIRSPerMO_r16 z, tt).
Definition MeasAndMobParametersFRX_Diff__ext4O__F2 (y : seq_type MeasAndMobParametersFRX_Diff__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__MeasAndMobParametersFRX_Diff__ext4O__Type i0
  end.
Lemma MeasAndMobParametersFRX_Diff__ext4O__F1F2_cond (z : MeasAndMobParametersFRX_Diff__ext4O__Type)
  : MeasAndMobParametersFRX_Diff__ext4O__cond z ->
  (seq_cond MeasAndMobParametersFRX_Diff__ext4O__list (MeasAndMobParametersFRX_Diff__ext4O__F1 z)).
intro H. unfold MeasAndMobParametersFRX_Diff__ext4O__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext4O__F1F2_cond2 (z : MeasAndMobParametersFRX_Diff__ext4O__Type)
 : MeasAndMobParametersFRX_Diff__ext4O__F2 (MeasAndMobParametersFRX_Diff__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersFRX_Diff__ext4O__F2F1_cond (y : seq_type MeasAndMobParametersFRX_Diff__ext4O__list)
  : seq_cond MeasAndMobParametersFRX_Diff__ext4O__list y ->
 (MeasAndMobParametersFRX_Diff__ext4O__cond (MeasAndMobParametersFRX_Diff__ext4O__F2 y)) /\  MeasAndMobParametersFRX_Diff__ext4O__F1 (MeasAndMobParametersFRX_Diff__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersFRX_Diff__ext4O__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersFRX_Diff__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersFRX_Diff__ext4O__Format : T_Format MeasAndMobParametersFRX_Diff__ext4O__Type MeasAndMobParametersFRX_Diff__ext4O__cond :=
        proj2_format  MeasAndMobParametersFRX_Diff__ext4O__cond MeasAndMobParametersFRX_Diff__ext4O__list__Format
    MeasAndMobParametersFRX_Diff__ext4O__F1 MeasAndMobParametersFRX_Diff__ext4O__F2 MeasAndMobParametersFRX_Diff__ext4O__F1F2_cond  MeasAndMobParametersFRX_Diff__ext4O__F1F2_cond2 MeasAndMobParametersFRX_Diff__ext4O__F2F1_cond.
Opaque MeasAndMobParametersFRX_Diff__ext4O__cond MeasAndMobParametersFRX_Diff__ext4O__Format.

Definition MeasAndMobParametersFRX_Diff__ext4__check_all_none (b : MeasAndMobParametersFRX_Diff__ext4O__Type) : bool :=
match b with 
  | make__MeasAndMobParametersFRX_Diff__ext4O__Type None  => false 
  | _ => true 
 end.
Definition MeasAndMobParametersFRX_Diff__ext4__Format : T_Format MeasAndMobParametersFRX_Diff__ext4__Type MeasAndMobParametersFRX_Diff__ext4__cond :=
  restrict_add_format MeasAndMobParametersFRX_Diff__ext4__check_all_none MeasAndMobParametersFRX_Diff__ext4O__Format.

Opaque MeasAndMobParametersFRX_Diff__ext4__cond MeasAndMobParametersFRX_Diff__ext4__Format.


Definition MeasAndMobParametersFRX_Diff__root_Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersFRX_Diff__root_list.
Definition MeasAndMobParametersFRX_Diff__root_Format_list : MeasAndMobParametersFRX_Diff__root_Format_Type :=
  (MeasAndMobParametersFRX_Diff__ss_SINR_Meas__Format, (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB__Format, (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB__Format, (MeasAndMobParametersFRX_Diff__csi_SINR_Meas__Format, (MeasAndMobParametersFRX_Diff__csi_RS_RLM__Format, unit_format))))).

Definition MeasAndMobParametersFRX_Diff__ext_Format_Type := Eval cbn in get_formats MeasAndMobParametersFRX_Diff__ext_list.
Definition MeasAndMobParametersFRX_Diff__ext_Format_list : MeasAndMobParametersFRX_Diff__ext_Format_Type :=
  (MeasAndMobParametersFRX_Diff__ext0__Format, (MeasAndMobParametersFRX_Diff__ext1__Format, (MeasAndMobParametersFRX_Diff__ext2__Format, (MeasAndMobParametersFRX_Diff__ext3__Format, (MeasAndMobParametersFRX_Diff__ext4__Format, unit__Format))))).

Definition MeasAndMobParametersFRX_Diff__list_type : Set := (seq_type MeasAndMobParametersFRX_Diff__root_list) * (seq_ext_type MeasAndMobParametersFRX_Diff__ext_list).
Definition MeasAndMobParametersFRX_Diff__list_cond (z : MeasAndMobParametersFRX_Diff__list_type) : Prop :=
        (seq_cond MeasAndMobParametersFRX_Diff__root_list (fst z)) /\ (seq_ext_cond MeasAndMobParametersFRX_Diff__ext_list (snd z)).
Definition MeasAndMobParametersFRX_Diff__list_format : T_Format MeasAndMobParametersFRX_Diff__list_type MeasAndMobParametersFRX_Diff__list_cond :=
 (* Eval compute in *) seq_ext_format MeasAndMobParametersFRX_Diff__root_list MeasAndMobParametersFRX_Diff__root_Format_list MeasAndMobParametersFRX_Diff__ext_list MeasAndMobParametersFRX_Diff__ext_Format_list.

Opaque MeasAndMobParametersFRX_Diff__list_format.
Definition MeasAndMobParametersFRX_Diff__F1 (z : MeasAndMobParametersFRX_Diff__Type) : MeasAndMobParametersFRX_Diff__list_type :=
  (((MeasAndMobParametersFRX_Diff__ss_SINR_Meas z, (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithSSB z, (MeasAndMobParametersFRX_Diff__csi_RSRP_AndRSRQ_MeasWithoutSSB z, (MeasAndMobParametersFRX_Diff__csi_SINR_Meas z, (MeasAndMobParametersFRX_Diff__csi_RS_RLM z, tt)))))), (
(MeasAndMobParametersFRX_Diff__ext0 z, (MeasAndMobParametersFRX_Diff__ext1 z, (MeasAndMobParametersFRX_Diff__ext2 z, (MeasAndMobParametersFRX_Diff__ext3 z, (MeasAndMobParametersFRX_Diff__ext4 z, tt))))))).
Definition MeasAndMobParametersFRX_Diff__F2 (y : MeasAndMobParametersFRX_Diff__list_type) : MeasAndMobParametersFRX_Diff__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, (i1, (i2, (i3, (i4, _))))))=>
    make__MeasAndMobParametersFRX_Diff__Type j0 j1 j2 j3 j4 i0 i1 i2 i3 i4
  end.
Definition MeasAndMobParametersFRX_Diff__helper1 : (forall a : MeasAndMobParametersFRX_Diff__Type, MeasAndMobParametersFRX_Diff__cond a -> MeasAndMobParametersFRX_Diff__list_cond (MeasAndMobParametersFRX_Diff__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasAndMobParametersFRX_Diff__helper2 : (forall a : MeasAndMobParametersFRX_Diff__Type, MeasAndMobParametersFRX_Diff__F2 (MeasAndMobParametersFRX_Diff__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasAndMobParametersFRX_Diff__helper3 : (forall b : MeasAndMobParametersFRX_Diff__list_type, MeasAndMobParametersFRX_Diff__list_cond b -> MeasAndMobParametersFRX_Diff__cond (MeasAndMobParametersFRX_Diff__F2 b) /\ MeasAndMobParametersFRX_Diff__F1 (MeasAndMobParametersFRX_Diff__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasAndMobParametersFRX_Diff__cond, MeasAndMobParametersFRX_Diff__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasAndMobParametersFRX_Diff__Format : T_Format MeasAndMobParametersFRX_Diff__Type MeasAndMobParametersFRX_Diff__cond :=
 proj2_format MeasAndMobParametersFRX_Diff__cond MeasAndMobParametersFRX_Diff__list_format  MeasAndMobParametersFRX_Diff__F1 MeasAndMobParametersFRX_Diff__F2 MeasAndMobParametersFRX_Diff__helper1 MeasAndMobParametersFRX_Diff__helper2 MeasAndMobParametersFRX_Diff__helper3.

Opaque MeasAndMobParametersFRX_Diff__cond MeasAndMobParametersFRX_Diff__Format.

