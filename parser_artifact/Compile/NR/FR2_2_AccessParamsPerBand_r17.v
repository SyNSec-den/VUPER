Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Type, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F2 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F1 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Type, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F2 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F1 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Type, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F2 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F1 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F2 y) = y. enum_solve H y. Qed.

Record FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Type : Set :=
  make__FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Type {
    FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17 : option FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17 : option FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17 : option FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Type ;
}.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list := (
 Opt FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Type FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Type FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Type FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__cond ::
 nil).
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond z := 
  opt_cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__cond (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__cond (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__cond (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17 z) /\
  True.

Inductive FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Type, (FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F2 (FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F1 (FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Type, (FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F2 (FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F1 (FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Type, (FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F2 (FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F1 (FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Record FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Type : Set :=
  make__FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Type {
    FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17 : option FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17 : option FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type ;
}.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list := (
 Opt FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__cond ::
 nil).
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond z := 
  opt_cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17 z) /\
  True.

Inductive FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Record FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Type : Set :=
  make__FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Type {
    FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17 : option FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17 : option FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type ;
}.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list := (
 Opt FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__cond ::
 nil).
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond z := 
  opt_cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17 z) /\
  True.

Inductive FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Type : Set :=
 | FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__supported
.
Definition FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__cond := (fun (_ : FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Type) => True).
Lemma FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__nat__helper.

Definition FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F1 t :=
  match t with
  | FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__supported => 0
  end.
Definition FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F2 n :=
  match n with
  | 0 => FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__supported
  | _ => FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__supported
  end.
Lemma FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F1F2 : forall x : FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Type, (FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F1 x <= 0) /\ FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F2 (FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F1 x) = x. imp_solve. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F2F1 : forall (y : nat) (H : y <= 0), FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F1 (FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F2 y) = y. enum_solve H y. Qed.

Record FR2_2_AccessParamsPerBand_r17__ext0O__Type : Set :=
  make__FR2_2_AccessParamsPerBand_r17__ext0O__Type {
    FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17 : option FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Type ;
}.
Definition FR2_2_AccessParamsPerBand_r17__ext0O__list := (
 Opt FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Type FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__cond ::
 nil).
Definition FR2_2_AccessParamsPerBand_r17__ext0O__cond z := 
  opt_cond FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__cond (FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17 z) /\
  True.

Definition FR2_2_AccessParamsPerBand_r17__ext0__Type := FR2_2_AccessParamsPerBand_r17__ext0O__Type.
Definition FR2_2_AccessParamsPerBand_r17__ext0__cond := FR2_2_AccessParamsPerBand_r17__ext0O__cond.

Record FR2_2_AccessParamsPerBand_r17__Type : Set :=
  make__FR2_2_AccessParamsPerBand_r17__Type {
    FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17 : option FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17 : option FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17 : option FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17 : option FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17 : option FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17 : option FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17 : option FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17 : option FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17 : option FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17 : option FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17 : option FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17 : option FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17 : option FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17 : option FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17 : option FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17 : option FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Type ;
    FR2_2_AccessParamsPerBand_r17__ext0 : option FR2_2_AccessParamsPerBand_r17__ext0__Type ;
}.
Definition FR2_2_AccessParamsPerBand_r17__root_list : list seq_elem := (
 Opt FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Type FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Type FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Type FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Type FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Type FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Type FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Type FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Type FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Type FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Type FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Type FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Type FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Type FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Type FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Type FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond ::
 nil).
Definition FR2_2_AccessParamsPerBand_r17__ext_list : list typ := (
  typ_cons FR2_2_AccessParamsPerBand_r17__ext0__Type FR2_2_AccessParamsPerBand_r17__ext0__cond ::
  nil).
Definition FR2_2_AccessParamsPerBand_r17__cond (z : FR2_2_AccessParamsPerBand_r17__Type) := 
(  opt_cond FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__cond (FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__cond (FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__cond (FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17 z) /\
  True) /\ 
(  opt_cond FR2_2_AccessParamsPerBand_r17__ext0__cond (FR2_2_AccessParamsPerBand_r17__ext0 z) /\
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
Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__cond FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__cond FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__cond FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__cond FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__cond FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__cond FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__cond FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__cond FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__nat__Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F1 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F1F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__nat__Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F1 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F1F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__nat__Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F1 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F1F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Format.


Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Format_Type := Eval cbn in seq_format_prod FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Format_list : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Format_Type :=
  (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17__Format, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17__Format, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17__Format, unit_format))).
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list__Format := (*Eval compute in *) seq_format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Format_list.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1 z :=
  (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_1_r17 z, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring4_2_r17 z, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__pdcch_monitoring8_4_r17 z, tt))).
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F2 (y : seq_type FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Type i0 i1 i2
  end.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1F2_cond (z : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Type)
  : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond z ->
  (seq_cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1 z)).
intro H. unfold FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond in H. simpl. auto. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1F2_cond2 (z : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Type)
 : FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F2 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F2F1_cond (y : seq_type FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list)
  : seq_cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list y ->
 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F2 y)) /\  FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1 (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond. simpl in *. auto.
 - simpl. unfold FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Type FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond :=
        proj2_format  FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__list__Format
    FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1F2_cond  FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F1F2_cond2 FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__F2F1_cond.
Opaque FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__cond FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__nat__Format FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F1 FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F2 FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F1F2 FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__cond FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__nat__Format FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F1 FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F2 FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F1F2 FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__cond FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__nat__Format FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F1 FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F2 FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F1F2 FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__cond FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Format.


Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Format_Type := Eval cbn in seq_format_prod FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Format_list : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Format_Type :=
  (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Format, unit_format))).
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list__Format := (*Eval compute in *) seq_format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Format_list.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1 z :=
  (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17 z, tt))).
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F2 (y : seq_type FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Type i0 i1 i2
  end.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1F2_cond (z : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Type)
  : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond z ->
  (seq_cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1 z)).
intro H. unfold FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond in H. simpl. auto. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1F2_cond2 (z : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Type)
 : FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F2 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F2F1_cond (y : seq_type FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list)
  : seq_cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list y ->
 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F2 y)) /\  FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1 (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond. simpl in *. auto.
 - simpl. unfold FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Type FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond :=
        proj2_format  FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__list__Format
    FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F2 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1F2_cond  FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F1F2_cond2 FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__F2F1_cond.
Opaque FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__cond FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__nat__Format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F1F2 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Format.


Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Format_Type := Eval cbn in seq_format_prod FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Format_list : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Format_Type :=
  (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17__Format, unit_format))).
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list__Format := (*Eval compute in *) seq_format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Format_list.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1 z :=
  (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_480kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__scs_960kHz_r17 z, tt))).
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F2 (y : seq_type FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Type i0 i1 i2
  end.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1F2_cond (z : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Type)
  : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond z ->
  (seq_cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1 z)).
intro H. unfold FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond in H. simpl. auto. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1F2_cond2 (z : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Type)
 : FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F2 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F2F1_cond (y : seq_type FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list)
  : seq_cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list y ->
 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F2 y)) /\  FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1 (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond. simpl in *. auto.
 - simpl. unfold FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Type FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond :=
        proj2_format  FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__list__Format
    FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F2 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1F2_cond  FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F1F2_cond2 FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__F2F1_cond.
Opaque FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__cond FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Format.

Definition FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__nat__Format FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F1 FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F2 FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F1F2 FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__F2F1.

Opaque FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__cond FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Format.


Definition FR2_2_AccessParamsPerBand_r17__ext0O__Format_Type := Eval cbn in seq_format_prod FR2_2_AccessParamsPerBand_r17__ext0O__list.
Definition FR2_2_AccessParamsPerBand_r17__ext0O__Format_list : FR2_2_AccessParamsPerBand_r17__ext0O__Format_Type :=
  (FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17__Format, unit_format).
Definition FR2_2_AccessParamsPerBand_r17__ext0O__list__Format := (*Eval compute in *) seq_format FR2_2_AccessParamsPerBand_r17__ext0O__list FR2_2_AccessParamsPerBand_r17__ext0O__Format_list.
Definition FR2_2_AccessParamsPerBand_r17__ext0O__F1 z :=
  (FR2_2_AccessParamsPerBand_r17__ext0O__modulation64_QAM_PUSCH_FR2_2_r17 z, tt).
Definition FR2_2_AccessParamsPerBand_r17__ext0O__F2 (y : seq_type FR2_2_AccessParamsPerBand_r17__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__FR2_2_AccessParamsPerBand_r17__ext0O__Type i0
  end.
Lemma FR2_2_AccessParamsPerBand_r17__ext0O__F1F2_cond (z : FR2_2_AccessParamsPerBand_r17__ext0O__Type)
  : FR2_2_AccessParamsPerBand_r17__ext0O__cond z ->
  (seq_cond FR2_2_AccessParamsPerBand_r17__ext0O__list (FR2_2_AccessParamsPerBand_r17__ext0O__F1 z)).
intro H. unfold FR2_2_AccessParamsPerBand_r17__ext0O__cond in H. simpl. auto. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__ext0O__F1F2_cond2 (z : FR2_2_AccessParamsPerBand_r17__ext0O__Type)
 : FR2_2_AccessParamsPerBand_r17__ext0O__F2 (FR2_2_AccessParamsPerBand_r17__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FR2_2_AccessParamsPerBand_r17__ext0O__F2F1_cond (y : seq_type FR2_2_AccessParamsPerBand_r17__ext0O__list)
  : seq_cond FR2_2_AccessParamsPerBand_r17__ext0O__list y ->
 (FR2_2_AccessParamsPerBand_r17__ext0O__cond (FR2_2_AccessParamsPerBand_r17__ext0O__F2 y)) /\  FR2_2_AccessParamsPerBand_r17__ext0O__F1 (FR2_2_AccessParamsPerBand_r17__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FR2_2_AccessParamsPerBand_r17__ext0O__cond. simpl in *. auto.
 - simpl. unfold FR2_2_AccessParamsPerBand_r17__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FR2_2_AccessParamsPerBand_r17__ext0O__Format : T_Format FR2_2_AccessParamsPerBand_r17__ext0O__Type FR2_2_AccessParamsPerBand_r17__ext0O__cond :=
        proj2_format  FR2_2_AccessParamsPerBand_r17__ext0O__cond FR2_2_AccessParamsPerBand_r17__ext0O__list__Format
    FR2_2_AccessParamsPerBand_r17__ext0O__F1 FR2_2_AccessParamsPerBand_r17__ext0O__F2 FR2_2_AccessParamsPerBand_r17__ext0O__F1F2_cond  FR2_2_AccessParamsPerBand_r17__ext0O__F1F2_cond2 FR2_2_AccessParamsPerBand_r17__ext0O__F2F1_cond.
Opaque FR2_2_AccessParamsPerBand_r17__ext0O__cond FR2_2_AccessParamsPerBand_r17__ext0O__Format.

Definition FR2_2_AccessParamsPerBand_r17__ext0__check_all_none (b : FR2_2_AccessParamsPerBand_r17__ext0O__Type) : bool :=
match b with 
  | make__FR2_2_AccessParamsPerBand_r17__ext0O__Type None  => false 
  | _ => true 
 end.
Definition FR2_2_AccessParamsPerBand_r17__ext0__Format : T_Format FR2_2_AccessParamsPerBand_r17__ext0__Type FR2_2_AccessParamsPerBand_r17__ext0__cond :=
  restrict_add_format FR2_2_AccessParamsPerBand_r17__ext0__check_all_none FR2_2_AccessParamsPerBand_r17__ext0O__Format.

Opaque FR2_2_AccessParamsPerBand_r17__ext0__cond FR2_2_AccessParamsPerBand_r17__ext0__Format.


Definition FR2_2_AccessParamsPerBand_r17__root_Format_Type := Eval cbn in seq_format_prod FR2_2_AccessParamsPerBand_r17__root_list.
Definition FR2_2_AccessParamsPerBand_r17__root_Format_list : FR2_2_AccessParamsPerBand_r17__root_Format_Type :=
  (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17__Format, (FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17__Format, (FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17__Format, (FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17__Format, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17__Format, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17__Format, unit_format)))))))))))))))))))))).

Definition FR2_2_AccessParamsPerBand_r17__ext_Format_Type := Eval cbn in get_formats FR2_2_AccessParamsPerBand_r17__ext_list.
Definition FR2_2_AccessParamsPerBand_r17__ext_Format_list : FR2_2_AccessParamsPerBand_r17__ext_Format_Type :=
  (FR2_2_AccessParamsPerBand_r17__ext0__Format, unit__Format).

Definition FR2_2_AccessParamsPerBand_r17__list_type : Set := (seq_type FR2_2_AccessParamsPerBand_r17__root_list) * (seq_ext_type FR2_2_AccessParamsPerBand_r17__ext_list).
Definition FR2_2_AccessParamsPerBand_r17__list_cond (z : FR2_2_AccessParamsPerBand_r17__list_type) : Prop :=
        (seq_cond FR2_2_AccessParamsPerBand_r17__root_list (fst z)) /\ (seq_ext_cond FR2_2_AccessParamsPerBand_r17__ext_list (snd z)).
Definition FR2_2_AccessParamsPerBand_r17__list_format : T_Format FR2_2_AccessParamsPerBand_r17__list_type FR2_2_AccessParamsPerBand_r17__list_cond :=
 (* Eval compute in *) seq_ext_format FR2_2_AccessParamsPerBand_r17__root_list FR2_2_AccessParamsPerBand_r17__root_Format_list FR2_2_AccessParamsPerBand_r17__ext_list FR2_2_AccessParamsPerBand_r17__ext_Format_list.

Opaque FR2_2_AccessParamsPerBand_r17__list_format.
Definition FR2_2_AccessParamsPerBand_r17__F1 (z : FR2_2_AccessParamsPerBand_r17__Type) : FR2_2_AccessParamsPerBand_r17__list_type :=
  (((FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__multiPDSCH_SingleDCI_FR2_2_SCS_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__multiPUSCH_SingleDCI_FR2_2_SCS_120kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_480kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_480kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__initialAccessSSB_480kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__widebandPRACH_SCS_480kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_480kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_480kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__dl_FR2_2_SCS_960kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__ul_FR2_2_SCS_960kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__multiRB_PUCCH_SCS_960kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__enhancedPDCCH_monitoringSCS_960kHz_r17 z, (FR2_2_AccessParamsPerBand_r17__type1_ChannelAccess_FR2_2_r17 z, (FR2_2_AccessParamsPerBand_r17__type2_ChannelAccess_FR2_2_r17 z, (FR2_2_AccessParamsPerBand_r17__reduced_BeamSwitchTiming_FR2_2_r17 z, (FR2_2_AccessParamsPerBand_r17__support32_DL_HARQ_ProcessPerSCS_r17 z, (FR2_2_AccessParamsPerBand_r17__support32_UL_HARQ_ProcessPerSCS_r17 z, tt))))))))))))))))))))))), (
(FR2_2_AccessParamsPerBand_r17__ext0 z, tt))).
Definition FR2_2_AccessParamsPerBand_r17__F2 (y : FR2_2_AccessParamsPerBand_r17__list_type) : FR2_2_AccessParamsPerBand_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, (j18, (j19, (j20, (j21, _)))))))))))))))))))))), (i0, _))=>
    make__FR2_2_AccessParamsPerBand_r17__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 i0
  end.
Definition FR2_2_AccessParamsPerBand_r17__helper1 : (forall a : FR2_2_AccessParamsPerBand_r17__Type, FR2_2_AccessParamsPerBand_r17__cond a -> FR2_2_AccessParamsPerBand_r17__list_cond (FR2_2_AccessParamsPerBand_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition FR2_2_AccessParamsPerBand_r17__helper2 : (forall a : FR2_2_AccessParamsPerBand_r17__Type, FR2_2_AccessParamsPerBand_r17__F2 (FR2_2_AccessParamsPerBand_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition FR2_2_AccessParamsPerBand_r17__helper3 : (forall b : FR2_2_AccessParamsPerBand_r17__list_type, FR2_2_AccessParamsPerBand_r17__list_cond b -> FR2_2_AccessParamsPerBand_r17__cond (FR2_2_AccessParamsPerBand_r17__F2 b) /\ FR2_2_AccessParamsPerBand_r17__F1 (FR2_2_AccessParamsPerBand_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold FR2_2_AccessParamsPerBand_r17__cond, FR2_2_AccessParamsPerBand_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition FR2_2_AccessParamsPerBand_r17__Format : T_Format FR2_2_AccessParamsPerBand_r17__Type FR2_2_AccessParamsPerBand_r17__cond :=
 proj2_format FR2_2_AccessParamsPerBand_r17__cond FR2_2_AccessParamsPerBand_r17__list_format  FR2_2_AccessParamsPerBand_r17__F1 FR2_2_AccessParamsPerBand_r17__F2 FR2_2_AccessParamsPerBand_r17__helper1 FR2_2_AccessParamsPerBand_r17__helper2 FR2_2_AccessParamsPerBand_r17__helper3.

Opaque FR2_2_AccessParamsPerBand_r17__cond FR2_2_AccessParamsPerBand_r17__Format.

