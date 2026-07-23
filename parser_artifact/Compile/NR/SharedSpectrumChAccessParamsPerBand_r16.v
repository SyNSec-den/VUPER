Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__helper1 : (1 <= 5)%Z.  lia. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__helper2 : to_bit_sz (Z.to_nat (5 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__Type := Z.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__cond := (fun z => (1 <= z <= 5)%Z).
Inductive SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__dummy__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__dummy__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__dummy__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__dummy__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__dummy__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__dummy__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__dummy__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__dummy__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__dummy__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__dummy__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__dummy__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__dummy__Type, (SharedSpectrumChAccessParamsPerBand_r16__dummy__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__dummy__F2 (SharedSpectrumChAccessParamsPerBand_r16__dummy__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__dummy__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__dummy__F1 (SharedSpectrumChAccessParamsPerBand_r16__dummy__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Type : Set :=
 | SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__supported
.
Definition SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__cond := (fun (_ : SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Type) => True).
Lemma SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__nat__helper.

Definition SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F1 t :=
  match t with
  | SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__supported => 0
  end.
Definition SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F2 n :=
  match n with
  | 0 => SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__supported
  | _ => SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__supported
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F1F2 : forall x : SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Type, (SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F1 x <= 0) /\ SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F1 x) = x. imp_solve. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F2F1 : forall (y : nat) (H : y <= 0), SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F2 y) = y. enum_solve H y. Qed.

Record SharedSpectrumChAccessParamsPerBand_r16__Type : Set :=
  make__SharedSpectrumChAccessParamsPerBand_r16__Type {
    SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16 : option SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16 : option SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16 : option SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16 : option SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16 : option SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16 : option SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16 : option Z ;
    SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16 : option SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16 : option SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16 : option SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16 : option SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16 : option SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16 : option SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16 : option SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16 : option SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16 : option SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16 : option SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16 : option SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16 : option SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16 : option SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16 : option SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16 : option SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__dummy : option SharedSpectrumChAccessParamsPerBand_r16__dummy__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16 : option SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16 : option SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16 : option SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16 : option SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16 : option SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16 : option SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16 : option SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16 : option SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Type ;
    SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16 : option SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Type ;
}.
Definition SharedSpectrumChAccessParamsPerBand_r16__list := (
 Opt SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Type SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Type SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Type SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Type SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Type SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Type SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__cond ::
 Opt Z SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Type SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Type SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Type SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Type SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Type SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Type SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Type SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Type SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Type SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Type SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Type SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Type SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Type SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Type SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Type SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__dummy__Type SharedSpectrumChAccessParamsPerBand_r16__dummy__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Type SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Type SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Type SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Type SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Type SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Type SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Type SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Type SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Type SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__cond ::
 nil).
Definition SharedSpectrumChAccessParamsPerBand_r16__cond z := 
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__dummy__cond (SharedSpectrumChAccessParamsPerBand_r16__dummy z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16 z) /\
  True.


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
Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__cond SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__cond SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__cond SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__cond SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__cond SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__cond SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__Format : T_Format Z SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__cond :=
 ranged_int_format (1) (5) SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__helper1 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__helper2.

Opaque SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__cond SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__cond SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__cond SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__cond SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__cond SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__cond SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__cond SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__cond SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__cond SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__cond SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__cond SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__cond SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__cond SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__cond SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__cond SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__cond SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__dummy__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__dummy__nat__Format SharedSpectrumChAccessParamsPerBand_r16__dummy__F1 SharedSpectrumChAccessParamsPerBand_r16__dummy__F2 SharedSpectrumChAccessParamsPerBand_r16__dummy__F1F2 SharedSpectrumChAccessParamsPerBand_r16__dummy__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__dummy__cond SharedSpectrumChAccessParamsPerBand_r16__dummy__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__cond SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__cond SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__cond SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__cond SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__cond SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__cond SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__cond SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__cond SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Format.

Definition SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__nat__Format SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F1F2 SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__F2F1.

Opaque SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__cond SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Format.


Definition SharedSpectrumChAccessParamsPerBand_r16__Format_Type := Eval cbn in seq_format_prod SharedSpectrumChAccessParamsPerBand_r16__list.
Definition SharedSpectrumChAccessParamsPerBand_r16__Format_list : SharedSpectrumChAccessParamsPerBand_r16__Format_Type :=
  (SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__dummy__Format, (SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16__Format, (SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16__Format, unit_format)))))))))))))))))))))))))))))))))))))))))).
Definition SharedSpectrumChAccessParamsPerBand_r16__list__Format := (*Eval compute in *) seq_format SharedSpectrumChAccessParamsPerBand_r16__list SharedSpectrumChAccessParamsPerBand_r16__Format_list.
Definition SharedSpectrumChAccessParamsPerBand_r16__F1 z :=
  (SharedSpectrumChAccessParamsPerBand_r16__ul_DynamicChAccess_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ul_Semi_StaticChAccess_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_DynamicChAccess_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RRM_Semi_StaticChAccess_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__mib_Acquisition_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_DynamicChAccess_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ssb_RLM_Semi_StaticChAccess_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__sib1_Acquisition_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__extRA_ResponseWindow_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_dynamicChannelAccess_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ssb_BFD_CBD_semi_staticChannelAccess_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_BFD_CBD_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ul_ChannelBW_SCell_10mhz_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__rssi_ChannelOccupancyReporting_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__srs_StartAnyOFDM_Symbol_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceFreqMonitorLocation_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__coreset_RB_Offset_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__cgi_Acquisition_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__configuredUL_Tx_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__prach_Wideband_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__dci_AvailableRB_Set_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__dci_ChOccupancyDuration_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__typeB_PDSCH_length_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithDCI_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchWithoutDCI_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__searchSpaceSwitchCapability2_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__non_numericalPDSCH_HARQ_timing_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__enhancedDynamicHARQ_codebook_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__oneShotHARQ_feedback_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__multiPUSCH_UL_grant_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__csi_RS_RLM_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__dummy z, (SharedSpectrumChAccessParamsPerBand_r16__periodicAndSemi_PersistentCSI_RS_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__pusch_PRB_interlace_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__pucch_F0_F1_PRB_Interlace_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__occ_PRB_PF2_PF3_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__extCP_rangeCG_PUSCH_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__configuredGrantWithReTx_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ed_Threshold_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__ul_DL_COT_Sharing_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__mux_CG_UCI_HARQ_ACK_r16 z, (SharedSpectrumChAccessParamsPerBand_r16__cg_resourceConfig_r16 z, tt)))))))))))))))))))))))))))))))))))))))))).
Definition SharedSpectrumChAccessParamsPerBand_r16__F2 (y : seq_type SharedSpectrumChAccessParamsPerBand_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, (i24, (i25, (i26, (i27, (i28, (i29, (i30, (i31, (i32, (i33, (i34, (i35, (i36, (i37, (i38, (i39, (i40, (i41, _))))))))))))))))))))))))))))))))))))))))))=>
    make__SharedSpectrumChAccessParamsPerBand_r16__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32 i33 i34 i35 i36 i37 i38 i39 i40 i41
  end.
Lemma SharedSpectrumChAccessParamsPerBand_r16__F1F2_cond (z : SharedSpectrumChAccessParamsPerBand_r16__Type)
  : SharedSpectrumChAccessParamsPerBand_r16__cond z ->
  (seq_cond SharedSpectrumChAccessParamsPerBand_r16__list (SharedSpectrumChAccessParamsPerBand_r16__F1 z)).
intro H. unfold SharedSpectrumChAccessParamsPerBand_r16__cond in H. simpl. auto. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__F1F2_cond2 (z : SharedSpectrumChAccessParamsPerBand_r16__Type)
 : SharedSpectrumChAccessParamsPerBand_r16__F2 (SharedSpectrumChAccessParamsPerBand_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SharedSpectrumChAccessParamsPerBand_r16__F2F1_cond (y : seq_type SharedSpectrumChAccessParamsPerBand_r16__list)
  : seq_cond SharedSpectrumChAccessParamsPerBand_r16__list y ->
 (SharedSpectrumChAccessParamsPerBand_r16__cond (SharedSpectrumChAccessParamsPerBand_r16__F2 y)) /\  SharedSpectrumChAccessParamsPerBand_r16__F1 (SharedSpectrumChAccessParamsPerBand_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SharedSpectrumChAccessParamsPerBand_r16__cond. simpl in *. auto.
 - simpl. unfold SharedSpectrumChAccessParamsPerBand_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SharedSpectrumChAccessParamsPerBand_r16__Format : T_Format SharedSpectrumChAccessParamsPerBand_r16__Type SharedSpectrumChAccessParamsPerBand_r16__cond :=
        proj2_format  SharedSpectrumChAccessParamsPerBand_r16__cond SharedSpectrumChAccessParamsPerBand_r16__list__Format
    SharedSpectrumChAccessParamsPerBand_r16__F1 SharedSpectrumChAccessParamsPerBand_r16__F2 SharedSpectrumChAccessParamsPerBand_r16__F1F2_cond  SharedSpectrumChAccessParamsPerBand_r16__F1F2_cond2 SharedSpectrumChAccessParamsPerBand_r16__F2F1_cond.
Opaque SharedSpectrumChAccessParamsPerBand_r16__cond SharedSpectrumChAccessParamsPerBand_r16__Format.

