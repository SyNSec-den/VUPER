Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Type : Set :=
 | CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__supported
.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__cond := (fun (_ : CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Type) => True).
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__nat__helper.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__supported
  | _ => CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__supported
  end.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F1F2 : forall x : CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Type, (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F2 (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F1 (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F2 y) = y. enum_solve H y. Qed.

Inductive CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Type : Set :=
 | CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__supported
.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__cond := (fun (_ : CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Type) => True).
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__nat__helper.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__supported
  | _ => CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__supported
  end.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F1F2 : forall x : CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Type, (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F2 (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F1 (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F2 y) = y. enum_solve H y. Qed.

Inductive CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Type : Set :=
 | CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__supported
.
Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__cond := (fun (_ : CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Type) => True).
Lemma CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__nat__helper.

Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__supported
  | _ => CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__supported
  end.
Lemma CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F1F2 : forall x : CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Type, (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F2 (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F1 (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F2 y) = y. enum_solve H y. Qed.

Inductive CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Type : Set :=
 | CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__supported
.
Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__cond := (fun (_ : CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Type) => True).
Lemma CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__nat__helper.

Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__supported
  | _ => CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__supported
  end.
Lemma CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F1F2 : forall x : CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Type, (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F2 (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F1 (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F2 y) = y. enum_solve H y. Qed.

Inductive CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Type : Set :=
 | CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__supported
.
Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__cond := (fun (_ : CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Type) => True).
Lemma CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__nat__helper.

Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__supported
  | _ => CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__supported
  end.
Lemma CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F1F2 : forall x : CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Type, (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F2 (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F1 (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F2 y) = y. enum_solve H y. Qed.

Inductive CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Type : Set :=
 | CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__supported
.
Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__cond := (fun (_ : CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Type) => True).
Lemma CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__nat__helper.

Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__supported
  | _ => CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__supported
  end.
Lemma CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F1F2 : forall x : CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Type, (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F2 (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F1 (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F2 y) = y. enum_solve H y. Qed.

Inductive CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Type : Set :=
 | CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__supported
.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__cond := (fun (_ : CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Type) => True).
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__nat__helper.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__supported
  | _ => CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__supported
  end.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F1F2 : forall x : CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Type, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F2 (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F1 (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F2 y) = y. enum_solve H y. Qed.

Inductive CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Type : Set :=
 | CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__supported
.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__cond := (fun (_ : CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Type) => True).
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__nat__helper.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__supported
  | _ => CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__supported
  end.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F1F2 : forall x : CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Type, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F2 (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F1 (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F2 y) = y. enum_solve H y. Qed.

Inductive CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Type : Set :=
 | CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__supported
.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__cond := (fun (_ : CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Type) => True).
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__nat__helper.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F1 t :=
  match t with
  | CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__supported => 0
  end.
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F2 n :=
  match n with
  | 0 => CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__supported
  | _ => CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__supported
  end.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F1F2 : forall x : CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Type, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F1 x <= 0) /\ CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F2 (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F1 x) = x. imp_solve. Qed.
Lemma CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F2F1 : forall (y : nat) (H : y <= 0), CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F1 (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F2 y) = y. enum_solve H y. Qed.

Record CarrierAggregationVariant__Type : Set :=
  make__CarrierAggregationVariant__Type {
    CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD : option CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Type ;
    CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD : option CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Type ;
    CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD : option CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Type ;
    CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD : option CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Type ;
    CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD : option CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Type ;
    CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD : option CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Type ;
    CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD : option CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Type ;
    CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD : option CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Type ;
    CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD : option CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Type ;
}.
Definition CarrierAggregationVariant__list := (
 Opt CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Type CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__cond ::
 Opt CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Type CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__cond ::
 Opt CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Type CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__cond ::
 Opt CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Type CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__cond ::
 Opt CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Type CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__cond ::
 Opt CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Type CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__cond ::
 Opt CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Type CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__cond ::
 Opt CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Type CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__cond ::
 Opt CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Type CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__cond ::
 nil).
Definition CarrierAggregationVariant__cond z := 
  opt_cond CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__cond (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD z) /\
  opt_cond CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__cond (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD z) /\
  opt_cond CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__cond (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD z) /\
  opt_cond CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__cond (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD z) /\
  opt_cond CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__cond (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD z) /\
  opt_cond CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__cond (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD z) /\
  opt_cond CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__cond (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD z) /\
  opt_cond CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__cond (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD z) /\
  opt_cond CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__cond (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD z) /\
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
Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Format : T_Format CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__nat__Format CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F1 CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F2 CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F1F2 CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__F2F1.

Opaque CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__cond CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Format.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Format : T_Format CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__nat__Format CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F1 CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F2 CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F1F2 CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__F2F1.

Opaque CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__cond CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Format.

Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Format : T_Format CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__nat__Format CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F1 CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F2 CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F1F2 CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__F2F1.

Opaque CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__cond CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Format.

Definition CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Format : T_Format CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__nat__Format CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F1 CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F2 CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F1F2 CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__F2F1.

Opaque CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__cond CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Format.

Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Format : T_Format CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__nat__Format CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F1 CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F2 CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F1F2 CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__F2F1.

Opaque CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__cond CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Format.

Definition CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Format : T_Format CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__nat__Format CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F1 CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F2 CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F1F2 CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__F2F1.

Opaque CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__cond CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Format.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Format : T_Format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__nat__Format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F1 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F2 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F1F2 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__F2F1.

Opaque CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__cond CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Format.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Format : T_Format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__nat__Format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F1 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F2 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F1F2 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__F2F1.

Opaque CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__cond CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Format.

Definition CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Format : T_Format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__nat__Format CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F1 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F2 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F1F2 CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__F2F1.

Opaque CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__cond CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Format.


Definition CarrierAggregationVariant__Format_Type := Eval cbn in seq_format_prod CarrierAggregationVariant__list.
Definition CarrierAggregationVariant__Format_list : CarrierAggregationVariant__Format_Type :=
  (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD__Format, (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD__Format, (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD__Format, (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD__Format, (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD__Format, (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD__Format, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD__Format, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD__Format, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD__Format, unit_format))))))))).
Definition CarrierAggregationVariant__list__Format := (*Eval compute in *) seq_format CarrierAggregationVariant__list CarrierAggregationVariant__Format_list.
Definition CarrierAggregationVariant__F1 z :=
  (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1FDD z, (CarrierAggregationVariant__fr1fdd_FR1TDD_CA_SpCellOnFR1TDD z, (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR1FDD z, (CarrierAggregationVariant__fr1fdd_FR2TDD_CA_SpCellOnFR2TDD z, (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR1TDD z, (CarrierAggregationVariant__fr1tdd_FR2TDD_CA_SpCellOnFR2TDD z, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1FDD z, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR1TDD z, (CarrierAggregationVariant__fr1fdd_FR1TDD_FR2TDD_CA_SpCellOnFR2TDD z, tt))))))))).
Definition CarrierAggregationVariant__F2 (y : seq_type CarrierAggregationVariant__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _)))))))))=>
    make__CarrierAggregationVariant__Type i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Lemma CarrierAggregationVariant__F1F2_cond (z : CarrierAggregationVariant__Type)
  : CarrierAggregationVariant__cond z ->
  (seq_cond CarrierAggregationVariant__list (CarrierAggregationVariant__F1 z)).
intro H. unfold CarrierAggregationVariant__cond in H. simpl. auto. Qed.
Lemma CarrierAggregationVariant__F1F2_cond2 (z : CarrierAggregationVariant__Type)
 : CarrierAggregationVariant__F2 (CarrierAggregationVariant__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CarrierAggregationVariant__F2F1_cond (y : seq_type CarrierAggregationVariant__list)
  : seq_cond CarrierAggregationVariant__list y ->
 (CarrierAggregationVariant__cond (CarrierAggregationVariant__F2 y)) /\  CarrierAggregationVariant__F1 (CarrierAggregationVariant__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CarrierAggregationVariant__cond. simpl in *. auto.
 - simpl. unfold CarrierAggregationVariant__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CarrierAggregationVariant__Format : T_Format CarrierAggregationVariant__Type CarrierAggregationVariant__cond :=
        proj2_format  CarrierAggregationVariant__cond CarrierAggregationVariant__list__Format
    CarrierAggregationVariant__F1 CarrierAggregationVariant__F2 CarrierAggregationVariant__F1F2_cond  CarrierAggregationVariant__F1F2_cond2 CarrierAggregationVariant__F2F1_cond.
Opaque CarrierAggregationVariant__cond CarrierAggregationVariant__Format.

