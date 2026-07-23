Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Record PDCP_Parameters__supportedROHC_Profiles__Type : Set :=
  make__PDCP_Parameters__supportedROHC_Profiles__Type {
    PDCP_Parameters__supportedROHC_Profiles__profile0x0000 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0001 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0002 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0003 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0004 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0006 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0101 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0102 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0103 : bool ;
    PDCP_Parameters__supportedROHC_Profiles__profile0x0104 : bool ;
}.
Definition PDCP_Parameters__supportedROHC_Profiles__list := (
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 nil).
Definition PDCP_Parameters__supportedROHC_Profiles__cond z := 
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0000 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0001 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0002 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0003 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0004 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0006 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0101 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0102 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0103 z) /\
  (fun _ => True) (PDCP_Parameters__supportedROHC_Profiles__profile0x0104 z) /\
  True.

Inductive PDCP_Parameters__maxNumberROHC_ContextSessions__Type : Set :=
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs2
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs4
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs8
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs12
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs16
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs24
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs32
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs48
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs64
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs128
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs256
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs512
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs1024
 | PDCP_Parameters__maxNumberROHC_ContextSessions__cs16384
 | PDCP_Parameters__maxNumberROHC_ContextSessions__spare2
 | PDCP_Parameters__maxNumberROHC_ContextSessions__spare1
.
Definition PDCP_Parameters__maxNumberROHC_ContextSessions__cond := (fun (_ : PDCP_Parameters__maxNumberROHC_ContextSessions__Type) => True).
Lemma PDCP_Parameters__maxNumberROHC_ContextSessions__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__maxNumberROHC_ContextSessions__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 PDCP_Parameters__maxNumberROHC_ContextSessions__nat__helper.

Definition PDCP_Parameters__maxNumberROHC_ContextSessions__F1 t :=
  match t with
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs2 => 0
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs4 => 1
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs8 => 2
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs12 => 3
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs16 => 4
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs24 => 5
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs32 => 6
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs48 => 7
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs64 => 8
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs128 => 9
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs256 => 10
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs512 => 11
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs1024 => 12
  | PDCP_Parameters__maxNumberROHC_ContextSessions__cs16384 => 13
  | PDCP_Parameters__maxNumberROHC_ContextSessions__spare2 => 14
  | PDCP_Parameters__maxNumberROHC_ContextSessions__spare1 => 15
  end.
Definition PDCP_Parameters__maxNumberROHC_ContextSessions__F2 n :=
  match n with
  | 0 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs2
  | 1 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs4
  | 2 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs8
  | 3 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs12
  | 4 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs16
  | 5 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs24
  | 6 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs32
  | 7 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs48
  | 8 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs64
  | 9 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs128
  | 10 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs256
  | 11 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs512
  | 12 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs1024
  | 13 => PDCP_Parameters__maxNumberROHC_ContextSessions__cs16384
  | 14 => PDCP_Parameters__maxNumberROHC_ContextSessions__spare2
  | 15 => PDCP_Parameters__maxNumberROHC_ContextSessions__spare1
  | _ => PDCP_Parameters__maxNumberROHC_ContextSessions__cs2
  end.
Lemma PDCP_Parameters__maxNumberROHC_ContextSessions__F1F2 : forall x : PDCP_Parameters__maxNumberROHC_ContextSessions__Type, (PDCP_Parameters__maxNumberROHC_ContextSessions__F1 x <= 15) /\ PDCP_Parameters__maxNumberROHC_ContextSessions__F2 (PDCP_Parameters__maxNumberROHC_ContextSessions__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__maxNumberROHC_ContextSessions__F2F1 : forall (y : nat) (H : y <= 15), PDCP_Parameters__maxNumberROHC_ContextSessions__F1 (PDCP_Parameters__maxNumberROHC_ContextSessions__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__uplinkOnlyROHC_Profiles__Type : Set :=
 | PDCP_Parameters__uplinkOnlyROHC_Profiles__supported
.
Definition PDCP_Parameters__uplinkOnlyROHC_Profiles__cond := (fun (_ : PDCP_Parameters__uplinkOnlyROHC_Profiles__Type) => True).
Lemma PDCP_Parameters__uplinkOnlyROHC_Profiles__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__uplinkOnlyROHC_Profiles__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__uplinkOnlyROHC_Profiles__nat__helper.

Definition PDCP_Parameters__uplinkOnlyROHC_Profiles__F1 t :=
  match t with
  | PDCP_Parameters__uplinkOnlyROHC_Profiles__supported => 0
  end.
Definition PDCP_Parameters__uplinkOnlyROHC_Profiles__F2 n :=
  match n with
  | 0 => PDCP_Parameters__uplinkOnlyROHC_Profiles__supported
  | _ => PDCP_Parameters__uplinkOnlyROHC_Profiles__supported
  end.
Lemma PDCP_Parameters__uplinkOnlyROHC_Profiles__F1F2 : forall x : PDCP_Parameters__uplinkOnlyROHC_Profiles__Type, (PDCP_Parameters__uplinkOnlyROHC_Profiles__F1 x <= 0) /\ PDCP_Parameters__uplinkOnlyROHC_Profiles__F2 (PDCP_Parameters__uplinkOnlyROHC_Profiles__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__uplinkOnlyROHC_Profiles__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__uplinkOnlyROHC_Profiles__F1 (PDCP_Parameters__uplinkOnlyROHC_Profiles__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__continueROHC_Context__Type : Set :=
 | PDCP_Parameters__continueROHC_Context__supported
.
Definition PDCP_Parameters__continueROHC_Context__cond := (fun (_ : PDCP_Parameters__continueROHC_Context__Type) => True).
Lemma PDCP_Parameters__continueROHC_Context__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__continueROHC_Context__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__continueROHC_Context__nat__helper.

Definition PDCP_Parameters__continueROHC_Context__F1 t :=
  match t with
  | PDCP_Parameters__continueROHC_Context__supported => 0
  end.
Definition PDCP_Parameters__continueROHC_Context__F2 n :=
  match n with
  | 0 => PDCP_Parameters__continueROHC_Context__supported
  | _ => PDCP_Parameters__continueROHC_Context__supported
  end.
Lemma PDCP_Parameters__continueROHC_Context__F1F2 : forall x : PDCP_Parameters__continueROHC_Context__Type, (PDCP_Parameters__continueROHC_Context__F1 x <= 0) /\ PDCP_Parameters__continueROHC_Context__F2 (PDCP_Parameters__continueROHC_Context__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__continueROHC_Context__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__continueROHC_Context__F1 (PDCP_Parameters__continueROHC_Context__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__outOfOrderDelivery__Type : Set :=
 | PDCP_Parameters__outOfOrderDelivery__supported
.
Definition PDCP_Parameters__outOfOrderDelivery__cond := (fun (_ : PDCP_Parameters__outOfOrderDelivery__Type) => True).
Lemma PDCP_Parameters__outOfOrderDelivery__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__outOfOrderDelivery__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__outOfOrderDelivery__nat__helper.

Definition PDCP_Parameters__outOfOrderDelivery__F1 t :=
  match t with
  | PDCP_Parameters__outOfOrderDelivery__supported => 0
  end.
Definition PDCP_Parameters__outOfOrderDelivery__F2 n :=
  match n with
  | 0 => PDCP_Parameters__outOfOrderDelivery__supported
  | _ => PDCP_Parameters__outOfOrderDelivery__supported
  end.
Lemma PDCP_Parameters__outOfOrderDelivery__F1F2 : forall x : PDCP_Parameters__outOfOrderDelivery__Type, (PDCP_Parameters__outOfOrderDelivery__F1 x <= 0) /\ PDCP_Parameters__outOfOrderDelivery__F2 (PDCP_Parameters__outOfOrderDelivery__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__outOfOrderDelivery__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__outOfOrderDelivery__F1 (PDCP_Parameters__outOfOrderDelivery__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__shortSN__Type : Set :=
 | PDCP_Parameters__shortSN__supported
.
Definition PDCP_Parameters__shortSN__cond := (fun (_ : PDCP_Parameters__shortSN__Type) => True).
Lemma PDCP_Parameters__shortSN__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__shortSN__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__shortSN__nat__helper.

Definition PDCP_Parameters__shortSN__F1 t :=
  match t with
  | PDCP_Parameters__shortSN__supported => 0
  end.
Definition PDCP_Parameters__shortSN__F2 n :=
  match n with
  | 0 => PDCP_Parameters__shortSN__supported
  | _ => PDCP_Parameters__shortSN__supported
  end.
Lemma PDCP_Parameters__shortSN__F1F2 : forall x : PDCP_Parameters__shortSN__Type, (PDCP_Parameters__shortSN__F1 x <= 0) /\ PDCP_Parameters__shortSN__F2 (PDCP_Parameters__shortSN__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__shortSN__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__shortSN__F1 (PDCP_Parameters__shortSN__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__pdcp_DuplicationSRB__Type : Set :=
 | PDCP_Parameters__pdcp_DuplicationSRB__supported
.
Definition PDCP_Parameters__pdcp_DuplicationSRB__cond := (fun (_ : PDCP_Parameters__pdcp_DuplicationSRB__Type) => True).
Lemma PDCP_Parameters__pdcp_DuplicationSRB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__pdcp_DuplicationSRB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__pdcp_DuplicationSRB__nat__helper.

Definition PDCP_Parameters__pdcp_DuplicationSRB__F1 t :=
  match t with
  | PDCP_Parameters__pdcp_DuplicationSRB__supported => 0
  end.
Definition PDCP_Parameters__pdcp_DuplicationSRB__F2 n :=
  match n with
  | 0 => PDCP_Parameters__pdcp_DuplicationSRB__supported
  | _ => PDCP_Parameters__pdcp_DuplicationSRB__supported
  end.
Lemma PDCP_Parameters__pdcp_DuplicationSRB__F1F2 : forall x : PDCP_Parameters__pdcp_DuplicationSRB__Type, (PDCP_Parameters__pdcp_DuplicationSRB__F1 x <= 0) /\ PDCP_Parameters__pdcp_DuplicationSRB__F2 (PDCP_Parameters__pdcp_DuplicationSRB__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__pdcp_DuplicationSRB__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__pdcp_DuplicationSRB__F1 (PDCP_Parameters__pdcp_DuplicationSRB__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Type : Set :=
 | PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__supported
.
Definition PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__cond := (fun (_ : PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Type) => True).
Lemma PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__nat__helper.

Definition PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F1 t :=
  match t with
  | PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__supported => 0
  end.
Definition PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F2 n :=
  match n with
  | 0 => PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__supported
  | _ => PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__supported
  end.
Lemma PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F1F2 : forall x : PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Type, (PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F1 x <= 0) /\ PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F2 (PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F1 (PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext0O__drb_IAB_r16__Type : Set :=
 | PDCP_Parameters__ext0O__drb_IAB_r16__supported
.
Definition PDCP_Parameters__ext0O__drb_IAB_r16__cond := (fun (_ : PDCP_Parameters__ext0O__drb_IAB_r16__Type) => True).
Lemma PDCP_Parameters__ext0O__drb_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext0O__drb_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext0O__drb_IAB_r16__nat__helper.

Definition PDCP_Parameters__ext0O__drb_IAB_r16__F1 t :=
  match t with
  | PDCP_Parameters__ext0O__drb_IAB_r16__supported => 0
  end.
Definition PDCP_Parameters__ext0O__drb_IAB_r16__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext0O__drb_IAB_r16__supported
  | _ => PDCP_Parameters__ext0O__drb_IAB_r16__supported
  end.
Lemma PDCP_Parameters__ext0O__drb_IAB_r16__F1F2 : forall x : PDCP_Parameters__ext0O__drb_IAB_r16__Type, (PDCP_Parameters__ext0O__drb_IAB_r16__F1 x <= 0) /\ PDCP_Parameters__ext0O__drb_IAB_r16__F2 (PDCP_Parameters__ext0O__drb_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext0O__drb_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext0O__drb_IAB_r16__F1 (PDCP_Parameters__ext0O__drb_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext0O__non_DRB_IAB_r16__Type : Set :=
 | PDCP_Parameters__ext0O__non_DRB_IAB_r16__supported
.
Definition PDCP_Parameters__ext0O__non_DRB_IAB_r16__cond := (fun (_ : PDCP_Parameters__ext0O__non_DRB_IAB_r16__Type) => True).
Lemma PDCP_Parameters__ext0O__non_DRB_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext0O__non_DRB_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext0O__non_DRB_IAB_r16__nat__helper.

Definition PDCP_Parameters__ext0O__non_DRB_IAB_r16__F1 t :=
  match t with
  | PDCP_Parameters__ext0O__non_DRB_IAB_r16__supported => 0
  end.
Definition PDCP_Parameters__ext0O__non_DRB_IAB_r16__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext0O__non_DRB_IAB_r16__supported
  | _ => PDCP_Parameters__ext0O__non_DRB_IAB_r16__supported
  end.
Lemma PDCP_Parameters__ext0O__non_DRB_IAB_r16__F1F2 : forall x : PDCP_Parameters__ext0O__non_DRB_IAB_r16__Type, (PDCP_Parameters__ext0O__non_DRB_IAB_r16__F1 x <= 0) /\ PDCP_Parameters__ext0O__non_DRB_IAB_r16__F2 (PDCP_Parameters__ext0O__non_DRB_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext0O__non_DRB_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext0O__non_DRB_IAB_r16__F1 (PDCP_Parameters__ext0O__non_DRB_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Type : Set :=
 | PDCP_Parameters__ext0O__extendedDiscardTimer_r16__supported
.
Definition PDCP_Parameters__ext0O__extendedDiscardTimer_r16__cond := (fun (_ : PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Type) => True).
Lemma PDCP_Parameters__ext0O__extendedDiscardTimer_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext0O__extendedDiscardTimer_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext0O__extendedDiscardTimer_r16__nat__helper.

Definition PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F1 t :=
  match t with
  | PDCP_Parameters__ext0O__extendedDiscardTimer_r16__supported => 0
  end.
Definition PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext0O__extendedDiscardTimer_r16__supported
  | _ => PDCP_Parameters__ext0O__extendedDiscardTimer_r16__supported
  end.
Lemma PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F1F2 : forall x : PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Type, (PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F1 x <= 0) /\ PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F2 (PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F1 (PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext0O__continueEHC_Context_r16__Type : Set :=
 | PDCP_Parameters__ext0O__continueEHC_Context_r16__supported
.
Definition PDCP_Parameters__ext0O__continueEHC_Context_r16__cond := (fun (_ : PDCP_Parameters__ext0O__continueEHC_Context_r16__Type) => True).
Lemma PDCP_Parameters__ext0O__continueEHC_Context_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext0O__continueEHC_Context_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext0O__continueEHC_Context_r16__nat__helper.

Definition PDCP_Parameters__ext0O__continueEHC_Context_r16__F1 t :=
  match t with
  | PDCP_Parameters__ext0O__continueEHC_Context_r16__supported => 0
  end.
Definition PDCP_Parameters__ext0O__continueEHC_Context_r16__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext0O__continueEHC_Context_r16__supported
  | _ => PDCP_Parameters__ext0O__continueEHC_Context_r16__supported
  end.
Lemma PDCP_Parameters__ext0O__continueEHC_Context_r16__F1F2 : forall x : PDCP_Parameters__ext0O__continueEHC_Context_r16__Type, (PDCP_Parameters__ext0O__continueEHC_Context_r16__F1 x <= 0) /\ PDCP_Parameters__ext0O__continueEHC_Context_r16__F2 (PDCP_Parameters__ext0O__continueEHC_Context_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext0O__continueEHC_Context_r16__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext0O__continueEHC_Context_r16__F1 (PDCP_Parameters__ext0O__continueEHC_Context_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext0O__ehc_r16__Type : Set :=
 | PDCP_Parameters__ext0O__ehc_r16__supported
.
Definition PDCP_Parameters__ext0O__ehc_r16__cond := (fun (_ : PDCP_Parameters__ext0O__ehc_r16__Type) => True).
Lemma PDCP_Parameters__ext0O__ehc_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext0O__ehc_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext0O__ehc_r16__nat__helper.

Definition PDCP_Parameters__ext0O__ehc_r16__F1 t :=
  match t with
  | PDCP_Parameters__ext0O__ehc_r16__supported => 0
  end.
Definition PDCP_Parameters__ext0O__ehc_r16__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext0O__ehc_r16__supported
  | _ => PDCP_Parameters__ext0O__ehc_r16__supported
  end.
Lemma PDCP_Parameters__ext0O__ehc_r16__F1F2 : forall x : PDCP_Parameters__ext0O__ehc_r16__Type, (PDCP_Parameters__ext0O__ehc_r16__F1 x <= 0) /\ PDCP_Parameters__ext0O__ehc_r16__F2 (PDCP_Parameters__ext0O__ehc_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext0O__ehc_r16__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext0O__ehc_r16__F1 (PDCP_Parameters__ext0O__ehc_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Type : Set :=
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs2
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs4
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs8
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs16
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs32
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs64
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs128
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs256
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs512
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs1024
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs2048
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs4096
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs8192
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs16384
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs32768
 | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs65536
.
Definition PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cond := (fun (_ : PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Type) => True).
Lemma PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__nat__helper.

Definition PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F1 t :=
  match t with
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs2 => 0
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs4 => 1
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs8 => 2
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs16 => 3
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs32 => 4
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs64 => 5
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs128 => 6
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs256 => 7
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs512 => 8
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs1024 => 9
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs2048 => 10
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs4096 => 11
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs8192 => 12
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs16384 => 13
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs32768 => 14
  | PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs65536 => 15
  end.
Definition PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs2
  | 1 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs4
  | 2 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs8
  | 3 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs16
  | 4 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs32
  | 5 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs64
  | 6 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs128
  | 7 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs256
  | 8 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs512
  | 9 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs1024
  | 10 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs2048
  | 11 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs4096
  | 12 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs8192
  | 13 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs16384
  | 14 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs32768
  | 15 => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs65536
  | _ => PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cs2
  end.
Lemma PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F1F2 : forall x : PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Type, (PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F1 x <= 15) /\ PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F2 (PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F2F1 : forall (y : nat) (H : y <= 15), PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F1 (PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Type : Set :=
 | PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__supported
.
Definition PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__cond := (fun (_ : PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Type) => True).
Lemma PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__nat__helper.

Definition PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F1 t :=
  match t with
  | PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__supported => 0
  end.
Definition PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__supported
  | _ => PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__supported
  end.
Lemma PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F1F2 : forall x : PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Type, (PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F1 x <= 0) /\ PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F2 (PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F1 (PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Type : Set :=
 | PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__supported
.
Definition PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__cond := (fun (_ : PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Type) => True).
Lemma PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__nat__helper.

Definition PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F1 t :=
  match t with
  | PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__supported => 0
  end.
Definition PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__supported
  | _ => PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__supported
  end.
Lemma PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F1F2 : forall x : PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Type, (PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F1 x <= 0) /\ PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F2 (PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F1 (PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F2 y) = y. enum_solve H y. Qed.

Record PDCP_Parameters__ext0O__Type : Set :=
  make__PDCP_Parameters__ext0O__Type {
    PDCP_Parameters__ext0O__drb_IAB_r16 : option PDCP_Parameters__ext0O__drb_IAB_r16__Type ;
    PDCP_Parameters__ext0O__non_DRB_IAB_r16 : option PDCP_Parameters__ext0O__non_DRB_IAB_r16__Type ;
    PDCP_Parameters__ext0O__extendedDiscardTimer_r16 : option PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Type ;
    PDCP_Parameters__ext0O__continueEHC_Context_r16 : option PDCP_Parameters__ext0O__continueEHC_Context_r16__Type ;
    PDCP_Parameters__ext0O__ehc_r16 : option PDCP_Parameters__ext0O__ehc_r16__Type ;
    PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16 : option PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Type ;
    PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16 : option PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Type ;
    PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16 : option PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Type ;
}.
Definition PDCP_Parameters__ext0O__list := (
 Opt PDCP_Parameters__ext0O__drb_IAB_r16__Type PDCP_Parameters__ext0O__drb_IAB_r16__cond ::
 Opt PDCP_Parameters__ext0O__non_DRB_IAB_r16__Type PDCP_Parameters__ext0O__non_DRB_IAB_r16__cond ::
 Opt PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Type PDCP_Parameters__ext0O__extendedDiscardTimer_r16__cond ::
 Opt PDCP_Parameters__ext0O__continueEHC_Context_r16__Type PDCP_Parameters__ext0O__continueEHC_Context_r16__cond ::
 Opt PDCP_Parameters__ext0O__ehc_r16__Type PDCP_Parameters__ext0O__ehc_r16__cond ::
 Opt PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Type PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cond ::
 Opt PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Type PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__cond ::
 Opt PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Type PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__cond ::
 nil).
Definition PDCP_Parameters__ext0O__cond z := 
  opt_cond PDCP_Parameters__ext0O__drb_IAB_r16__cond (PDCP_Parameters__ext0O__drb_IAB_r16 z) /\
  opt_cond PDCP_Parameters__ext0O__non_DRB_IAB_r16__cond (PDCP_Parameters__ext0O__non_DRB_IAB_r16 z) /\
  opt_cond PDCP_Parameters__ext0O__extendedDiscardTimer_r16__cond (PDCP_Parameters__ext0O__extendedDiscardTimer_r16 z) /\
  opt_cond PDCP_Parameters__ext0O__continueEHC_Context_r16__cond (PDCP_Parameters__ext0O__continueEHC_Context_r16 z) /\
  opt_cond PDCP_Parameters__ext0O__ehc_r16__cond (PDCP_Parameters__ext0O__ehc_r16 z) /\
  opt_cond PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cond (PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16 z) /\
  opt_cond PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__cond (PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16 z) /\
  opt_cond PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__cond (PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16 z) /\
  True.

Definition PDCP_Parameters__ext0__Type := PDCP_Parameters__ext0O__Type.
Definition PDCP_Parameters__ext0__cond := PDCP_Parameters__ext0O__cond.

Inductive PDCP_Parameters__ext1O__longSN_RedCap_r17__Type : Set :=
 | PDCP_Parameters__ext1O__longSN_RedCap_r17__supported
.
Definition PDCP_Parameters__ext1O__longSN_RedCap_r17__cond := (fun (_ : PDCP_Parameters__ext1O__longSN_RedCap_r17__Type) => True).
Lemma PDCP_Parameters__ext1O__longSN_RedCap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext1O__longSN_RedCap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext1O__longSN_RedCap_r17__nat__helper.

Definition PDCP_Parameters__ext1O__longSN_RedCap_r17__F1 t :=
  match t with
  | PDCP_Parameters__ext1O__longSN_RedCap_r17__supported => 0
  end.
Definition PDCP_Parameters__ext1O__longSN_RedCap_r17__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext1O__longSN_RedCap_r17__supported
  | _ => PDCP_Parameters__ext1O__longSN_RedCap_r17__supported
  end.
Lemma PDCP_Parameters__ext1O__longSN_RedCap_r17__F1F2 : forall x : PDCP_Parameters__ext1O__longSN_RedCap_r17__Type, (PDCP_Parameters__ext1O__longSN_RedCap_r17__F1 x <= 0) /\ PDCP_Parameters__ext1O__longSN_RedCap_r17__F2 (PDCP_Parameters__ext1O__longSN_RedCap_r17__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext1O__longSN_RedCap_r17__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext1O__longSN_RedCap_r17__F1 (PDCP_Parameters__ext1O__longSN_RedCap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Type : Set :=
 | PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__supported
.
Definition PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__cond := (fun (_ : PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Type) => True).
Lemma PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__nat__helper.

Definition PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F1 t :=
  match t with
  | PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__supported => 0
  end.
Definition PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__supported
  | _ => PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__supported
  end.
Lemma PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F1F2 : forall x : PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Type, (PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F1 x <= 0) /\ PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F2 (PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F1 (PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F2 y) = y. enum_solve H y. Qed.

Lemma PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__Type := Z.
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__cond := (fun z => (0 <= z <= 15)%Z).
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Record PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Type : Set :=
  make__PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Type {
    PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17 : Z ;
    PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__associatedPLMN_ID_r17 : PLMN_Identity__Type ;
}.
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list := (
 Nor Z PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__cond ::
 Nor PLMN_Identity__Type PLMN_Identity__cond ::
 nil).
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond z := 
  PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__cond (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17 z) /\
  PLMN_Identity__cond (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__associatedPLMN_ID_r17 z) /\
  True.

Inductive PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Type : Set :=
 | PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__supported
.
Definition PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__cond := (fun (_ : PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Type) => True).
Lemma PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__nat__helper.

Definition PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F1 t :=
  match t with
  | PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__supported => 0
  end.
Definition PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__supported
  | _ => PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__supported
  end.
Lemma PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F1F2 : forall x : PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Type, (PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F1 x <= 0) /\ PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F2 (PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F1 (PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Type : Set :=
 | PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__kbyte4
 | PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__kbyte8
.
Definition PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__cond := (fun (_ : PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Type) => True).
Lemma PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__nat__helper.

Definition PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F1 t :=
  match t with
  | PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__kbyte4 => 0
  | PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__kbyte8 => 1
  end.
Definition PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F2 n :=
  match n with
  | 0 => PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__kbyte4
  | 1 => PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__kbyte8
  | _ => PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__kbyte4
  end.
Lemma PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F1F2 : forall x : PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Type, (PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F1 x <= 1) /\ PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F2 (PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F2F1 : forall (y : nat) (H : y <= 1), PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F1 (PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F2 y) = y. enum_solve H y. Qed.

Record PDCP_Parameters__ext1O__udc_r17__Type : Set :=
  make__PDCP_Parameters__ext1O__udc_r17__Type {
    PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17 : option PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Type ;
    PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17 : option PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Type ;
    PDCP_Parameters__ext1O__udc_r17__continueUDC_r17 : option PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Type ;
    PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17 : option PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Type ;
}.
Definition PDCP_Parameters__ext1O__udc_r17__list := (
 Opt PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Type PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__cond ::
 Opt PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Type PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond ::
 Opt PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Type PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__cond ::
 Opt PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Type PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__cond ::
 nil).
Definition PDCP_Parameters__ext1O__udc_r17__cond z := 
  opt_cond PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__cond (PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17 z) /\
  opt_cond PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17 z) /\
  opt_cond PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__cond (PDCP_Parameters__ext1O__udc_r17__continueUDC_r17 z) /\
  opt_cond PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__cond (PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17 z) /\
  True.

Record PDCP_Parameters__ext1O__Type : Set :=
  make__PDCP_Parameters__ext1O__Type {
    PDCP_Parameters__ext1O__longSN_RedCap_r17 : option PDCP_Parameters__ext1O__longSN_RedCap_r17__Type ;
    PDCP_Parameters__ext1O__udc_r17 : option PDCP_Parameters__ext1O__udc_r17__Type ;
}.
Definition PDCP_Parameters__ext1O__list := (
 Opt PDCP_Parameters__ext1O__longSN_RedCap_r17__Type PDCP_Parameters__ext1O__longSN_RedCap_r17__cond ::
 Opt PDCP_Parameters__ext1O__udc_r17__Type PDCP_Parameters__ext1O__udc_r17__cond ::
 nil).
Definition PDCP_Parameters__ext1O__cond z := 
  opt_cond PDCP_Parameters__ext1O__longSN_RedCap_r17__cond (PDCP_Parameters__ext1O__longSN_RedCap_r17 z) /\
  opt_cond PDCP_Parameters__ext1O__udc_r17__cond (PDCP_Parameters__ext1O__udc_r17 z) /\
  True.

Definition PDCP_Parameters__ext1__Type := PDCP_Parameters__ext1O__Type.
Definition PDCP_Parameters__ext1__cond := PDCP_Parameters__ext1O__cond.

Record PDCP_Parameters__Type : Set :=
  make__PDCP_Parameters__Type {
    PDCP_Parameters__supportedROHC_Profiles : PDCP_Parameters__supportedROHC_Profiles__Type ;
    PDCP_Parameters__maxNumberROHC_ContextSessions : PDCP_Parameters__maxNumberROHC_ContextSessions__Type ;
    PDCP_Parameters__uplinkOnlyROHC_Profiles : option PDCP_Parameters__uplinkOnlyROHC_Profiles__Type ;
    PDCP_Parameters__continueROHC_Context : option PDCP_Parameters__continueROHC_Context__Type ;
    PDCP_Parameters__outOfOrderDelivery : option PDCP_Parameters__outOfOrderDelivery__Type ;
    PDCP_Parameters__shortSN : option PDCP_Parameters__shortSN__Type ;
    PDCP_Parameters__pdcp_DuplicationSRB : option PDCP_Parameters__pdcp_DuplicationSRB__Type ;
    PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB : option PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Type ;
    PDCP_Parameters__ext0 : option PDCP_Parameters__ext0__Type ;
    PDCP_Parameters__ext1 : option PDCP_Parameters__ext1__Type ;
}.
Definition PDCP_Parameters__root_list : list seq_elem := (
 Nor PDCP_Parameters__supportedROHC_Profiles__Type PDCP_Parameters__supportedROHC_Profiles__cond ::
 Nor PDCP_Parameters__maxNumberROHC_ContextSessions__Type PDCP_Parameters__maxNumberROHC_ContextSessions__cond ::
 Opt PDCP_Parameters__uplinkOnlyROHC_Profiles__Type PDCP_Parameters__uplinkOnlyROHC_Profiles__cond ::
 Opt PDCP_Parameters__continueROHC_Context__Type PDCP_Parameters__continueROHC_Context__cond ::
 Opt PDCP_Parameters__outOfOrderDelivery__Type PDCP_Parameters__outOfOrderDelivery__cond ::
 Opt PDCP_Parameters__shortSN__Type PDCP_Parameters__shortSN__cond ::
 Opt PDCP_Parameters__pdcp_DuplicationSRB__Type PDCP_Parameters__pdcp_DuplicationSRB__cond ::
 Opt PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Type PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__cond ::
 nil).
Definition PDCP_Parameters__ext_list : list typ := (
  typ_cons PDCP_Parameters__ext0__Type PDCP_Parameters__ext0__cond ::
  typ_cons PDCP_Parameters__ext1__Type PDCP_Parameters__ext1__cond ::
  nil).
Definition PDCP_Parameters__cond (z : PDCP_Parameters__Type) := 
(  PDCP_Parameters__supportedROHC_Profiles__cond (PDCP_Parameters__supportedROHC_Profiles z) /\
  PDCP_Parameters__maxNumberROHC_ContextSessions__cond (PDCP_Parameters__maxNumberROHC_ContextSessions z) /\
  opt_cond PDCP_Parameters__uplinkOnlyROHC_Profiles__cond (PDCP_Parameters__uplinkOnlyROHC_Profiles z) /\
  opt_cond PDCP_Parameters__continueROHC_Context__cond (PDCP_Parameters__continueROHC_Context z) /\
  opt_cond PDCP_Parameters__outOfOrderDelivery__cond (PDCP_Parameters__outOfOrderDelivery z) /\
  opt_cond PDCP_Parameters__shortSN__cond (PDCP_Parameters__shortSN z) /\
  opt_cond PDCP_Parameters__pdcp_DuplicationSRB__cond (PDCP_Parameters__pdcp_DuplicationSRB z) /\
  opt_cond PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__cond (PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB z) /\
  True) /\ 
(  opt_cond PDCP_Parameters__ext0__cond (PDCP_Parameters__ext0 z) /\
  opt_cond PDCP_Parameters__ext1__cond (PDCP_Parameters__ext1 z) /\
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

Definition PDCP_Parameters__supportedROHC_Profiles__Format_Type := Eval cbn in seq_format_prod PDCP_Parameters__supportedROHC_Profiles__list.
Definition PDCP_Parameters__supportedROHC_Profiles__Format_list : PDCP_Parameters__supportedROHC_Profiles__Format_Type :=
  (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, unit_format)))))))))).
Definition PDCP_Parameters__supportedROHC_Profiles__list__Format := (*Eval compute in *) seq_format PDCP_Parameters__supportedROHC_Profiles__list PDCP_Parameters__supportedROHC_Profiles__Format_list.
Definition PDCP_Parameters__supportedROHC_Profiles__F1 z :=
  (PDCP_Parameters__supportedROHC_Profiles__profile0x0000 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0001 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0002 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0003 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0004 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0006 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0101 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0102 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0103 z, (PDCP_Parameters__supportedROHC_Profiles__profile0x0104 z, tt)))))))))).
Definition PDCP_Parameters__supportedROHC_Profiles__F2 (y : seq_type PDCP_Parameters__supportedROHC_Profiles__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__PDCP_Parameters__supportedROHC_Profiles__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma PDCP_Parameters__supportedROHC_Profiles__F1F2_cond (z : PDCP_Parameters__supportedROHC_Profiles__Type)
  : PDCP_Parameters__supportedROHC_Profiles__cond z ->
  (seq_cond PDCP_Parameters__supportedROHC_Profiles__list (PDCP_Parameters__supportedROHC_Profiles__F1 z)).
intro H. unfold PDCP_Parameters__supportedROHC_Profiles__cond in H. simpl. auto. Qed.
Lemma PDCP_Parameters__supportedROHC_Profiles__F1F2_cond2 (z : PDCP_Parameters__supportedROHC_Profiles__Type)
 : PDCP_Parameters__supportedROHC_Profiles__F2 (PDCP_Parameters__supportedROHC_Profiles__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Parameters__supportedROHC_Profiles__F2F1_cond (y : seq_type PDCP_Parameters__supportedROHC_Profiles__list)
  : seq_cond PDCP_Parameters__supportedROHC_Profiles__list y ->
 (PDCP_Parameters__supportedROHC_Profiles__cond (PDCP_Parameters__supportedROHC_Profiles__F2 y)) /\  PDCP_Parameters__supportedROHC_Profiles__F1 (PDCP_Parameters__supportedROHC_Profiles__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Parameters__supportedROHC_Profiles__cond. simpl in *. auto.
 - simpl. unfold PDCP_Parameters__supportedROHC_Profiles__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Parameters__supportedROHC_Profiles__Format : T_Format PDCP_Parameters__supportedROHC_Profiles__Type PDCP_Parameters__supportedROHC_Profiles__cond :=
        proj2_format  PDCP_Parameters__supportedROHC_Profiles__cond PDCP_Parameters__supportedROHC_Profiles__list__Format
    PDCP_Parameters__supportedROHC_Profiles__F1 PDCP_Parameters__supportedROHC_Profiles__F2 PDCP_Parameters__supportedROHC_Profiles__F1F2_cond  PDCP_Parameters__supportedROHC_Profiles__F1F2_cond2 PDCP_Parameters__supportedROHC_Profiles__F2F1_cond.
Opaque PDCP_Parameters__supportedROHC_Profiles__cond PDCP_Parameters__supportedROHC_Profiles__Format.

Definition PDCP_Parameters__maxNumberROHC_ContextSessions__Format : T_Format PDCP_Parameters__maxNumberROHC_ContextSessions__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__maxNumberROHC_ContextSessions__nat__Format PDCP_Parameters__maxNumberROHC_ContextSessions__F1 PDCP_Parameters__maxNumberROHC_ContextSessions__F2 PDCP_Parameters__maxNumberROHC_ContextSessions__F1F2 PDCP_Parameters__maxNumberROHC_ContextSessions__F2F1.

Opaque PDCP_Parameters__maxNumberROHC_ContextSessions__cond PDCP_Parameters__maxNumberROHC_ContextSessions__Format.

Definition PDCP_Parameters__uplinkOnlyROHC_Profiles__Format : T_Format PDCP_Parameters__uplinkOnlyROHC_Profiles__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__uplinkOnlyROHC_Profiles__nat__Format PDCP_Parameters__uplinkOnlyROHC_Profiles__F1 PDCP_Parameters__uplinkOnlyROHC_Profiles__F2 PDCP_Parameters__uplinkOnlyROHC_Profiles__F1F2 PDCP_Parameters__uplinkOnlyROHC_Profiles__F2F1.

Opaque PDCP_Parameters__uplinkOnlyROHC_Profiles__cond PDCP_Parameters__uplinkOnlyROHC_Profiles__Format.

Definition PDCP_Parameters__continueROHC_Context__Format : T_Format PDCP_Parameters__continueROHC_Context__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__continueROHC_Context__nat__Format PDCP_Parameters__continueROHC_Context__F1 PDCP_Parameters__continueROHC_Context__F2 PDCP_Parameters__continueROHC_Context__F1F2 PDCP_Parameters__continueROHC_Context__F2F1.

Opaque PDCP_Parameters__continueROHC_Context__cond PDCP_Parameters__continueROHC_Context__Format.

Definition PDCP_Parameters__outOfOrderDelivery__Format : T_Format PDCP_Parameters__outOfOrderDelivery__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__outOfOrderDelivery__nat__Format PDCP_Parameters__outOfOrderDelivery__F1 PDCP_Parameters__outOfOrderDelivery__F2 PDCP_Parameters__outOfOrderDelivery__F1F2 PDCP_Parameters__outOfOrderDelivery__F2F1.

Opaque PDCP_Parameters__outOfOrderDelivery__cond PDCP_Parameters__outOfOrderDelivery__Format.

Definition PDCP_Parameters__shortSN__Format : T_Format PDCP_Parameters__shortSN__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__shortSN__nat__Format PDCP_Parameters__shortSN__F1 PDCP_Parameters__shortSN__F2 PDCP_Parameters__shortSN__F1F2 PDCP_Parameters__shortSN__F2F1.

Opaque PDCP_Parameters__shortSN__cond PDCP_Parameters__shortSN__Format.

Definition PDCP_Parameters__pdcp_DuplicationSRB__Format : T_Format PDCP_Parameters__pdcp_DuplicationSRB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__pdcp_DuplicationSRB__nat__Format PDCP_Parameters__pdcp_DuplicationSRB__F1 PDCP_Parameters__pdcp_DuplicationSRB__F2 PDCP_Parameters__pdcp_DuplicationSRB__F1F2 PDCP_Parameters__pdcp_DuplicationSRB__F2F1.

Opaque PDCP_Parameters__pdcp_DuplicationSRB__cond PDCP_Parameters__pdcp_DuplicationSRB__Format.

Definition PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Format : T_Format PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__nat__Format PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F1 PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F2 PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F1F2 PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__F2F1.

Opaque PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__cond PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Format.

Definition PDCP_Parameters__ext0O__drb_IAB_r16__Format : T_Format PDCP_Parameters__ext0O__drb_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext0O__drb_IAB_r16__nat__Format PDCP_Parameters__ext0O__drb_IAB_r16__F1 PDCP_Parameters__ext0O__drb_IAB_r16__F2 PDCP_Parameters__ext0O__drb_IAB_r16__F1F2 PDCP_Parameters__ext0O__drb_IAB_r16__F2F1.

Opaque PDCP_Parameters__ext0O__drb_IAB_r16__cond PDCP_Parameters__ext0O__drb_IAB_r16__Format.

Definition PDCP_Parameters__ext0O__non_DRB_IAB_r16__Format : T_Format PDCP_Parameters__ext0O__non_DRB_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext0O__non_DRB_IAB_r16__nat__Format PDCP_Parameters__ext0O__non_DRB_IAB_r16__F1 PDCP_Parameters__ext0O__non_DRB_IAB_r16__F2 PDCP_Parameters__ext0O__non_DRB_IAB_r16__F1F2 PDCP_Parameters__ext0O__non_DRB_IAB_r16__F2F1.

Opaque PDCP_Parameters__ext0O__non_DRB_IAB_r16__cond PDCP_Parameters__ext0O__non_DRB_IAB_r16__Format.

Definition PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Format : T_Format PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext0O__extendedDiscardTimer_r16__nat__Format PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F1 PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F2 PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F1F2 PDCP_Parameters__ext0O__extendedDiscardTimer_r16__F2F1.

Opaque PDCP_Parameters__ext0O__extendedDiscardTimer_r16__cond PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Format.

Definition PDCP_Parameters__ext0O__continueEHC_Context_r16__Format : T_Format PDCP_Parameters__ext0O__continueEHC_Context_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext0O__continueEHC_Context_r16__nat__Format PDCP_Parameters__ext0O__continueEHC_Context_r16__F1 PDCP_Parameters__ext0O__continueEHC_Context_r16__F2 PDCP_Parameters__ext0O__continueEHC_Context_r16__F1F2 PDCP_Parameters__ext0O__continueEHC_Context_r16__F2F1.

Opaque PDCP_Parameters__ext0O__continueEHC_Context_r16__cond PDCP_Parameters__ext0O__continueEHC_Context_r16__Format.

Definition PDCP_Parameters__ext0O__ehc_r16__Format : T_Format PDCP_Parameters__ext0O__ehc_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext0O__ehc_r16__nat__Format PDCP_Parameters__ext0O__ehc_r16__F1 PDCP_Parameters__ext0O__ehc_r16__F2 PDCP_Parameters__ext0O__ehc_r16__F1F2 PDCP_Parameters__ext0O__ehc_r16__F2F1.

Opaque PDCP_Parameters__ext0O__ehc_r16__cond PDCP_Parameters__ext0O__ehc_r16__Format.

Definition PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Format : T_Format PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__nat__Format PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F1 PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F2 PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F1F2 PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__F2F1.

Opaque PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__cond PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Format.

Definition PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Format : T_Format PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__nat__Format PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F1 PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F2 PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F1F2 PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__F2F1.

Opaque PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__cond PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Format.

Definition PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Format : T_Format PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__nat__Format PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F1 PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F2 PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F1F2 PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__F2F1.

Opaque PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__cond PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Format.


Definition PDCP_Parameters__ext0O__Format_Type := Eval cbn in seq_format_prod PDCP_Parameters__ext0O__list.
Definition PDCP_Parameters__ext0O__Format_list : PDCP_Parameters__ext0O__Format_Type :=
  (PDCP_Parameters__ext0O__drb_IAB_r16__Format, (PDCP_Parameters__ext0O__non_DRB_IAB_r16__Format, (PDCP_Parameters__ext0O__extendedDiscardTimer_r16__Format, (PDCP_Parameters__ext0O__continueEHC_Context_r16__Format, (PDCP_Parameters__ext0O__ehc_r16__Format, (PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16__Format, (PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16__Format, (PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16__Format, unit_format)))))))).
Definition PDCP_Parameters__ext0O__list__Format := (*Eval compute in *) seq_format PDCP_Parameters__ext0O__list PDCP_Parameters__ext0O__Format_list.
Definition PDCP_Parameters__ext0O__F1 z :=
  (PDCP_Parameters__ext0O__drb_IAB_r16 z, (PDCP_Parameters__ext0O__non_DRB_IAB_r16 z, (PDCP_Parameters__ext0O__extendedDiscardTimer_r16 z, (PDCP_Parameters__ext0O__continueEHC_Context_r16 z, (PDCP_Parameters__ext0O__ehc_r16 z, (PDCP_Parameters__ext0O__maxNumberEHC_Contexts_r16 z, (PDCP_Parameters__ext0O__jointEHC_ROHC_Config_r16 z, (PDCP_Parameters__ext0O__pdcp_DuplicationMoreThanTwoRLC_r16 z, tt)))))))).
Definition PDCP_Parameters__ext0O__F2 (y : seq_type PDCP_Parameters__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__PDCP_Parameters__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma PDCP_Parameters__ext0O__F1F2_cond (z : PDCP_Parameters__ext0O__Type)
  : PDCP_Parameters__ext0O__cond z ->
  (seq_cond PDCP_Parameters__ext0O__list (PDCP_Parameters__ext0O__F1 z)).
intro H. unfold PDCP_Parameters__ext0O__cond in H. simpl. auto. Qed.
Lemma PDCP_Parameters__ext0O__F1F2_cond2 (z : PDCP_Parameters__ext0O__Type)
 : PDCP_Parameters__ext0O__F2 (PDCP_Parameters__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Parameters__ext0O__F2F1_cond (y : seq_type PDCP_Parameters__ext0O__list)
  : seq_cond PDCP_Parameters__ext0O__list y ->
 (PDCP_Parameters__ext0O__cond (PDCP_Parameters__ext0O__F2 y)) /\  PDCP_Parameters__ext0O__F1 (PDCP_Parameters__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Parameters__ext0O__cond. simpl in *. auto.
 - simpl. unfold PDCP_Parameters__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Parameters__ext0O__Format : T_Format PDCP_Parameters__ext0O__Type PDCP_Parameters__ext0O__cond :=
        proj2_format  PDCP_Parameters__ext0O__cond PDCP_Parameters__ext0O__list__Format
    PDCP_Parameters__ext0O__F1 PDCP_Parameters__ext0O__F2 PDCP_Parameters__ext0O__F1F2_cond  PDCP_Parameters__ext0O__F1F2_cond2 PDCP_Parameters__ext0O__F2F1_cond.
Opaque PDCP_Parameters__ext0O__cond PDCP_Parameters__ext0O__Format.

Definition PDCP_Parameters__ext0__check_all_none (b : PDCP_Parameters__ext0O__Type) : bool :=
match b with 
  | make__PDCP_Parameters__ext0O__Type None None None None None None None None  => false 
  | _ => true 
 end.
Definition PDCP_Parameters__ext0__Format : T_Format PDCP_Parameters__ext0__Type PDCP_Parameters__ext0__cond :=
  restrict_add_format PDCP_Parameters__ext0__check_all_none PDCP_Parameters__ext0O__Format.

Opaque PDCP_Parameters__ext0__cond PDCP_Parameters__ext0__Format.

Definition PDCP_Parameters__ext1O__longSN_RedCap_r17__Format : T_Format PDCP_Parameters__ext1O__longSN_RedCap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext1O__longSN_RedCap_r17__nat__Format PDCP_Parameters__ext1O__longSN_RedCap_r17__F1 PDCP_Parameters__ext1O__longSN_RedCap_r17__F2 PDCP_Parameters__ext1O__longSN_RedCap_r17__F1F2 PDCP_Parameters__ext1O__longSN_RedCap_r17__F2F1.

Opaque PDCP_Parameters__ext1O__longSN_RedCap_r17__cond PDCP_Parameters__ext1O__longSN_RedCap_r17__Format.

Definition PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Format : T_Format PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__nat__Format PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F1 PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F2 PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F1F2 PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__F2F1.

Opaque PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__cond PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Format.

Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__Format : T_Format Z PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__cond :=
 ranged_int_format (0) (15) PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__helper1 PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__helper2.

Opaque PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__cond PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__Format.


Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Format_Type := Eval cbn in seq_format_prod PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list.
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Format_list : PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Format_Type :=
  (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17__Format, (PLMN_Identity__Format, unit_format)).
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list__Format := (*Eval compute in *) seq_format PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Format_list.
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1 z :=
  (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__versionOfDictionary_r17 z, (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__associatedPLMN_ID_r17 z, tt)).
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F2 (y : seq_type PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Type i0 i1
  end.
Lemma PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1F2_cond (z : PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Type)
  : PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond z ->
  (seq_cond PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1 z)).
intro H. unfold PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond in H. simpl. auto. Qed.
Lemma PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1F2_cond2 (z : PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Type)
 : PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F2 (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F2F1_cond (y : seq_type PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list)
  : seq_cond PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list y ->
 (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F2 y)) /\  PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1 (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond. simpl in *. auto.
 - simpl. unfold PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Format : T_Format PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Type PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond :=
        proj2_format  PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__list__Format
    PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1 PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F2 PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1F2_cond  PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F1F2_cond2 PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__F2F1_cond.
Opaque PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__cond PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Format.

Definition PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Format : T_Format PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__nat__Format PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F1 PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F2 PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F1F2 PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__F2F1.

Opaque PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__cond PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Format.

Definition PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Format : T_Format PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__nat__Format PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F1 PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F2 PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F1F2 PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__F2F1.

Opaque PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__cond PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Format.


Definition PDCP_Parameters__ext1O__udc_r17__Format_Type := Eval cbn in seq_format_prod PDCP_Parameters__ext1O__udc_r17__list.
Definition PDCP_Parameters__ext1O__udc_r17__Format_list : PDCP_Parameters__ext1O__udc_r17__Format_Type :=
  (PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17__Format, (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17__Format, (PDCP_Parameters__ext1O__udc_r17__continueUDC_r17__Format, (PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17__Format, unit_format)))).
Definition PDCP_Parameters__ext1O__udc_r17__list__Format := (*Eval compute in *) seq_format PDCP_Parameters__ext1O__udc_r17__list PDCP_Parameters__ext1O__udc_r17__Format_list.
Definition PDCP_Parameters__ext1O__udc_r17__F1 z :=
  (PDCP_Parameters__ext1O__udc_r17__standardDictionary_r17 z, (PDCP_Parameters__ext1O__udc_r17__operatorDictionary_r17 z, (PDCP_Parameters__ext1O__udc_r17__continueUDC_r17 z, (PDCP_Parameters__ext1O__udc_r17__supportOfBufferSize_r17 z, tt)))).
Definition PDCP_Parameters__ext1O__udc_r17__F2 (y : seq_type PDCP_Parameters__ext1O__udc_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PDCP_Parameters__ext1O__udc_r17__Type i0 i1 i2 i3
  end.
Lemma PDCP_Parameters__ext1O__udc_r17__F1F2_cond (z : PDCP_Parameters__ext1O__udc_r17__Type)
  : PDCP_Parameters__ext1O__udc_r17__cond z ->
  (seq_cond PDCP_Parameters__ext1O__udc_r17__list (PDCP_Parameters__ext1O__udc_r17__F1 z)).
intro H. unfold PDCP_Parameters__ext1O__udc_r17__cond in H. simpl. auto. Qed.
Lemma PDCP_Parameters__ext1O__udc_r17__F1F2_cond2 (z : PDCP_Parameters__ext1O__udc_r17__Type)
 : PDCP_Parameters__ext1O__udc_r17__F2 (PDCP_Parameters__ext1O__udc_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Parameters__ext1O__udc_r17__F2F1_cond (y : seq_type PDCP_Parameters__ext1O__udc_r17__list)
  : seq_cond PDCP_Parameters__ext1O__udc_r17__list y ->
 (PDCP_Parameters__ext1O__udc_r17__cond (PDCP_Parameters__ext1O__udc_r17__F2 y)) /\  PDCP_Parameters__ext1O__udc_r17__F1 (PDCP_Parameters__ext1O__udc_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Parameters__ext1O__udc_r17__cond. simpl in *. auto.
 - simpl. unfold PDCP_Parameters__ext1O__udc_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Parameters__ext1O__udc_r17__Format : T_Format PDCP_Parameters__ext1O__udc_r17__Type PDCP_Parameters__ext1O__udc_r17__cond :=
        proj2_format  PDCP_Parameters__ext1O__udc_r17__cond PDCP_Parameters__ext1O__udc_r17__list__Format
    PDCP_Parameters__ext1O__udc_r17__F1 PDCP_Parameters__ext1O__udc_r17__F2 PDCP_Parameters__ext1O__udc_r17__F1F2_cond  PDCP_Parameters__ext1O__udc_r17__F1F2_cond2 PDCP_Parameters__ext1O__udc_r17__F2F1_cond.
Opaque PDCP_Parameters__ext1O__udc_r17__cond PDCP_Parameters__ext1O__udc_r17__Format.


Definition PDCP_Parameters__ext1O__Format_Type := Eval cbn in seq_format_prod PDCP_Parameters__ext1O__list.
Definition PDCP_Parameters__ext1O__Format_list : PDCP_Parameters__ext1O__Format_Type :=
  (PDCP_Parameters__ext1O__longSN_RedCap_r17__Format, (PDCP_Parameters__ext1O__udc_r17__Format, unit_format)).
Definition PDCP_Parameters__ext1O__list__Format := (*Eval compute in *) seq_format PDCP_Parameters__ext1O__list PDCP_Parameters__ext1O__Format_list.
Definition PDCP_Parameters__ext1O__F1 z :=
  (PDCP_Parameters__ext1O__longSN_RedCap_r17 z, (PDCP_Parameters__ext1O__udc_r17 z, tt)).
Definition PDCP_Parameters__ext1O__F2 (y : seq_type PDCP_Parameters__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDCP_Parameters__ext1O__Type i0 i1
  end.
Lemma PDCP_Parameters__ext1O__F1F2_cond (z : PDCP_Parameters__ext1O__Type)
  : PDCP_Parameters__ext1O__cond z ->
  (seq_cond PDCP_Parameters__ext1O__list (PDCP_Parameters__ext1O__F1 z)).
intro H. unfold PDCP_Parameters__ext1O__cond in H. simpl. auto. Qed.
Lemma PDCP_Parameters__ext1O__F1F2_cond2 (z : PDCP_Parameters__ext1O__Type)
 : PDCP_Parameters__ext1O__F2 (PDCP_Parameters__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Parameters__ext1O__F2F1_cond (y : seq_type PDCP_Parameters__ext1O__list)
  : seq_cond PDCP_Parameters__ext1O__list y ->
 (PDCP_Parameters__ext1O__cond (PDCP_Parameters__ext1O__F2 y)) /\  PDCP_Parameters__ext1O__F1 (PDCP_Parameters__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Parameters__ext1O__cond. simpl in *. auto.
 - simpl. unfold PDCP_Parameters__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Parameters__ext1O__Format : T_Format PDCP_Parameters__ext1O__Type PDCP_Parameters__ext1O__cond :=
        proj2_format  PDCP_Parameters__ext1O__cond PDCP_Parameters__ext1O__list__Format
    PDCP_Parameters__ext1O__F1 PDCP_Parameters__ext1O__F2 PDCP_Parameters__ext1O__F1F2_cond  PDCP_Parameters__ext1O__F1F2_cond2 PDCP_Parameters__ext1O__F2F1_cond.
Opaque PDCP_Parameters__ext1O__cond PDCP_Parameters__ext1O__Format.

Definition PDCP_Parameters__ext1__check_all_none (b : PDCP_Parameters__ext1O__Type) : bool :=
match b with 
  | make__PDCP_Parameters__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition PDCP_Parameters__ext1__Format : T_Format PDCP_Parameters__ext1__Type PDCP_Parameters__ext1__cond :=
  restrict_add_format PDCP_Parameters__ext1__check_all_none PDCP_Parameters__ext1O__Format.

Opaque PDCP_Parameters__ext1__cond PDCP_Parameters__ext1__Format.


Definition PDCP_Parameters__root_Format_Type := Eval cbn in seq_format_prod PDCP_Parameters__root_list.
Definition PDCP_Parameters__root_Format_list : PDCP_Parameters__root_Format_Type :=
  (PDCP_Parameters__supportedROHC_Profiles__Format, (PDCP_Parameters__maxNumberROHC_ContextSessions__Format, (PDCP_Parameters__uplinkOnlyROHC_Profiles__Format, (PDCP_Parameters__continueROHC_Context__Format, (PDCP_Parameters__outOfOrderDelivery__Format, (PDCP_Parameters__shortSN__Format, (PDCP_Parameters__pdcp_DuplicationSRB__Format, (PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB__Format, unit_format)))))))).

Definition PDCP_Parameters__ext_Format_Type := Eval cbn in get_formats PDCP_Parameters__ext_list.
Definition PDCP_Parameters__ext_Format_list : PDCP_Parameters__ext_Format_Type :=
  (PDCP_Parameters__ext0__Format, (PDCP_Parameters__ext1__Format, unit__Format)).

Definition PDCP_Parameters__list_type : Set := (seq_type PDCP_Parameters__root_list) * (seq_ext_type PDCP_Parameters__ext_list).
Definition PDCP_Parameters__list_cond (z : PDCP_Parameters__list_type) : Prop :=
        (seq_cond PDCP_Parameters__root_list (fst z)) /\ (seq_ext_cond PDCP_Parameters__ext_list (snd z)).
Definition PDCP_Parameters__list_format : T_Format PDCP_Parameters__list_type PDCP_Parameters__list_cond :=
 (* Eval compute in *) seq_ext_format PDCP_Parameters__root_list PDCP_Parameters__root_Format_list PDCP_Parameters__ext_list PDCP_Parameters__ext_Format_list.

Opaque PDCP_Parameters__list_format.
Definition PDCP_Parameters__F1 (z : PDCP_Parameters__Type) : PDCP_Parameters__list_type :=
  (((PDCP_Parameters__supportedROHC_Profiles z, (PDCP_Parameters__maxNumberROHC_ContextSessions z, (PDCP_Parameters__uplinkOnlyROHC_Profiles z, (PDCP_Parameters__continueROHC_Context z, (PDCP_Parameters__outOfOrderDelivery z, (PDCP_Parameters__shortSN z, (PDCP_Parameters__pdcp_DuplicationSRB z, (PDCP_Parameters__pdcp_DuplicationMCG_OrSCG_DRB z, tt))))))))), (
(PDCP_Parameters__ext0 z, (PDCP_Parameters__ext1 z, tt)))).
Definition PDCP_Parameters__F2 (y : PDCP_Parameters__list_type) : PDCP_Parameters__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, (i1, _)))=>
    make__PDCP_Parameters__Type j0 j1 j2 j3 j4 j5 j6 j7 i0 i1
  end.
Definition PDCP_Parameters__helper1 : (forall a : PDCP_Parameters__Type, PDCP_Parameters__cond a -> PDCP_Parameters__list_cond (PDCP_Parameters__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDCP_Parameters__helper2 : (forall a : PDCP_Parameters__Type, PDCP_Parameters__F2 (PDCP_Parameters__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDCP_Parameters__helper3 : (forall b : PDCP_Parameters__list_type, PDCP_Parameters__list_cond b -> PDCP_Parameters__cond (PDCP_Parameters__F2 b) /\ PDCP_Parameters__F1 (PDCP_Parameters__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDCP_Parameters__cond, PDCP_Parameters__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDCP_Parameters__Format : T_Format PDCP_Parameters__Type PDCP_Parameters__cond :=
 proj2_format PDCP_Parameters__cond PDCP_Parameters__list_format  PDCP_Parameters__F1 PDCP_Parameters__F2 PDCP_Parameters__helper1 PDCP_Parameters__helper2 PDCP_Parameters__helper3.

Opaque PDCP_Parameters__cond PDCP_Parameters__Format.

