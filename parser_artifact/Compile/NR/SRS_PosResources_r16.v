Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Type : Set :=
 | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n1
 | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n2
 | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n4
 | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n8
 | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n12
 | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n16
.
Definition SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__cond := (fun (_ : SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Type) => True).
Lemma SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__nat__helper.

Definition SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F1 t :=
  match t with
  | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n1 => 0
  | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n2 => 1
  | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n4 => 2
  | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n8 => 3
  | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n12 => 4
  | SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n16 => 5
  end.
Definition SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F2 n :=
  match n with
  | 0 => SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n1
  | 1 => SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n2
  | 2 => SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n4
  | 3 => SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n8
  | 4 => SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n12
  | 5 => SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n16
  | _ => SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__n1
  end.
Lemma SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F1F2 : forall x : SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Type, (SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F1 x <= 5) /\ SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F2 (SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F2F1 : forall (y : nat) (H : y <= 5), SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F1 (SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Type : Set :=
 | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n1
 | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n2
 | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n4
 | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n8
 | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n16
 | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n32
 | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n64
.
Definition SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__cond := (fun (_ : SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Type) => True).
Lemma SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__nat__helper.

Definition SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F1 t :=
  match t with
  | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n1 => 0
  | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n2 => 1
  | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n4 => 2
  | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n8 => 3
  | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n16 => 4
  | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n32 => 5
  | SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n64 => 6
  end.
Definition SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F2 n :=
  match n with
  | 0 => SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n1
  | 1 => SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n2
  | 2 => SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n4
  | 3 => SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n8
  | 4 => SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n16
  | 5 => SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n32
  | 6 => SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n64
  | _ => SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__n1
  end.
Lemma SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F1F2 : forall x : SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Type, (SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F1 x <= 6) /\ SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F2 (SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F2F1 : forall (y : nat) (H : y <= 6), SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F1 (SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Type : Set :=
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n1
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n2
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n3
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n4
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n5
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n6
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n8
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n10
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n12
 | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n14
.
Definition SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__cond := (fun (_ : SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Type) => True).
Lemma SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__nat__helper.

Definition SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F1 t :=
  match t with
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n1 => 0
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n2 => 1
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n3 => 2
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n4 => 3
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n5 => 4
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n6 => 5
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n8 => 6
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n10 => 7
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n12 => 8
  | SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n14 => 9
  end.
Definition SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F2 n :=
  match n with
  | 0 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n1
  | 1 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n2
  | 2 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n3
  | 3 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n4
  | 4 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n5
  | 5 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n6
  | 6 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n8
  | 7 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n10
  | 8 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n12
  | 9 => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n14
  | _ => SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__n1
  end.
Lemma SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F1F2 : forall x : SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Type, (SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F1 x <= 9) /\ SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F2 (SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F2F1 : forall (y : nat) (H : y <= 9), SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F1 (SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Type : Set :=
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n1
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n2
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n4
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n8
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n16
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n32
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n64
.
Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__cond := (fun (_ : SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Type) => True).
Lemma SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__nat__helper.

Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F1 t :=
  match t with
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n1 => 0
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n2 => 1
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n4 => 2
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n8 => 3
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n16 => 4
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n32 => 5
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n64 => 6
  end.
Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F2 n :=
  match n with
  | 0 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n1
  | 1 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n2
  | 2 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n4
  | 3 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n8
  | 4 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n16
  | 5 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n32
  | 6 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n64
  | _ => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__n1
  end.
Lemma SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F1F2 : forall x : SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Type, (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F1 x <= 6) /\ SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F2 (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F2F1 : forall (y : nat) (H : y <= 6), SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F1 (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Type : Set :=
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n1
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n2
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n3
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n4
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n5
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n6
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n8
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n10
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n12
 | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n14
.
Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__cond := (fun (_ : SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Type) => True).
Lemma SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__nat__helper.

Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F1 t :=
  match t with
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n1 => 0
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n2 => 1
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n3 => 2
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n4 => 3
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n5 => 4
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n6 => 5
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n8 => 6
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n10 => 7
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n12 => 8
  | SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n14 => 9
  end.
Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F2 n :=
  match n with
  | 0 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n1
  | 1 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n2
  | 2 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n3
  | 3 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n4
  | 4 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n5
  | 5 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n6
  | 6 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n8
  | 7 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n10
  | 8 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n12
  | 9 => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n14
  | _ => SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__n1
  end.
Lemma SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F1F2 : forall x : SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Type, (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F1 x <= 9) /\ SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F2 (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F2F1 : forall (y : nat) (H : y <= 9), SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F1 (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F2 y) = y. enum_solve H y. Qed.

Record SRS_PosResources_r16__Type : Set :=
  make__SRS_PosResources_r16__Type {
    SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16 : SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Type ;
    SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16 : SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Type ;
    SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16 : SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Type ;
    SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16 : SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Type ;
    SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16 : SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Type ;
}.
Definition SRS_PosResources_r16__list := (
 Nor SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Type SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__cond ::
 Nor SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Type SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__cond ::
 Nor SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Type SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__cond ::
 Nor SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Type SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__cond ::
 Nor SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Type SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__cond ::
 nil).
Definition SRS_PosResources_r16__cond z := 
  SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__cond (SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16 z) /\
  SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__cond (SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16 z) /\
  SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__cond (SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16 z) /\
  SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__cond (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16 z) /\
  SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__cond (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16 z) /\
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
Definition SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Format : T_Format SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__nat__Format SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F1 SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F2 SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F1F2 SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__F2F1.

Opaque SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__cond SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Format.

Definition SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Format : T_Format SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__nat__Format SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F1 SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F2 SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F1F2 SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__F2F1.

Opaque SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__cond SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Format.

Definition SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Format : T_Format SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__nat__Format SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F1 SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F2 SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F1F2 SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__F2F1.

Opaque SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__cond SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Format.

Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Format : T_Format SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__nat__Format SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F1 SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F2 SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F1F2 SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__F2F1.

Opaque SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__cond SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Format.

Definition SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Format : T_Format SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__nat__Format SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F1 SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F2 SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F1F2 SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__F2F1.

Opaque SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__cond SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Format.


Definition SRS_PosResources_r16__Format_Type := Eval cbn in seq_format_prod SRS_PosResources_r16__list.
Definition SRS_PosResources_r16__Format_list : SRS_PosResources_r16__Format_Type :=
  (SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16__Format, (SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16__Format, (SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16__Format, (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16__Format, (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16__Format, unit_format))))).
Definition SRS_PosResources_r16__list__Format := (*Eval compute in *) seq_format SRS_PosResources_r16__list SRS_PosResources_r16__Format_list.
Definition SRS_PosResources_r16__F1 z :=
  (SRS_PosResources_r16__maxNumberSRS_PosResourceSetPerBWP_r16 z, (SRS_PosResources_r16__maxNumberSRS_PosResourcesPerBWP_r16 z, (SRS_PosResources_r16__maxNumberSRS_ResourcesPerBWP_PerSlot_r16 z, (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_r16 z, (SRS_PosResources_r16__maxNumberPeriodicSRS_PosResourcesPerBWP_PerSlot_r16 z, tt))))).
Definition SRS_PosResources_r16__F2 (y : seq_type SRS_PosResources_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SRS_PosResources_r16__Type i0 i1 i2 i3 i4
  end.
Lemma SRS_PosResources_r16__F1F2_cond (z : SRS_PosResources_r16__Type)
  : SRS_PosResources_r16__cond z ->
  (seq_cond SRS_PosResources_r16__list (SRS_PosResources_r16__F1 z)).
intro H. unfold SRS_PosResources_r16__cond in H. simpl. auto. Qed.
Lemma SRS_PosResources_r16__F1F2_cond2 (z : SRS_PosResources_r16__Type)
 : SRS_PosResources_r16__F2 (SRS_PosResources_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_PosResources_r16__F2F1_cond (y : seq_type SRS_PosResources_r16__list)
  : seq_cond SRS_PosResources_r16__list y ->
 (SRS_PosResources_r16__cond (SRS_PosResources_r16__F2 y)) /\  SRS_PosResources_r16__F1 (SRS_PosResources_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_PosResources_r16__cond. simpl in *. auto.
 - simpl. unfold SRS_PosResources_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_PosResources_r16__Format : T_Format SRS_PosResources_r16__Type SRS_PosResources_r16__cond :=
        proj2_format  SRS_PosResources_r16__cond SRS_PosResources_r16__list__Format
    SRS_PosResources_r16__F1 SRS_PosResources_r16__F2 SRS_PosResources_r16__F1F2_cond  SRS_PosResources_r16__F1F2_cond2 SRS_PosResources_r16__F2F1_cond.
Opaque SRS_PosResources_r16__cond SRS_PosResources_r16__Format.

