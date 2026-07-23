Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PDCP_Config__drb__discardTimer__Type : Set :=
 | PDCP_Config__drb__discardTimer__ms10
 | PDCP_Config__drb__discardTimer__ms20
 | PDCP_Config__drb__discardTimer__ms30
 | PDCP_Config__drb__discardTimer__ms40
 | PDCP_Config__drb__discardTimer__ms50
 | PDCP_Config__drb__discardTimer__ms60
 | PDCP_Config__drb__discardTimer__ms75
 | PDCP_Config__drb__discardTimer__ms100
 | PDCP_Config__drb__discardTimer__ms150
 | PDCP_Config__drb__discardTimer__ms200
 | PDCP_Config__drb__discardTimer__ms250
 | PDCP_Config__drb__discardTimer__ms300
 | PDCP_Config__drb__discardTimer__ms500
 | PDCP_Config__drb__discardTimer__ms750
 | PDCP_Config__drb__discardTimer__ms1500
 | PDCP_Config__drb__discardTimer__infinity
.
Definition PDCP_Config__drb__discardTimer__cond := (fun (_ : PDCP_Config__drb__discardTimer__Type) => True).
Lemma PDCP_Config__drb__discardTimer__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__drb__discardTimer__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 PDCP_Config__drb__discardTimer__nat__helper.

Definition PDCP_Config__drb__discardTimer__F1 t :=
  match t with
  | PDCP_Config__drb__discardTimer__ms10 => 0
  | PDCP_Config__drb__discardTimer__ms20 => 1
  | PDCP_Config__drb__discardTimer__ms30 => 2
  | PDCP_Config__drb__discardTimer__ms40 => 3
  | PDCP_Config__drb__discardTimer__ms50 => 4
  | PDCP_Config__drb__discardTimer__ms60 => 5
  | PDCP_Config__drb__discardTimer__ms75 => 6
  | PDCP_Config__drb__discardTimer__ms100 => 7
  | PDCP_Config__drb__discardTimer__ms150 => 8
  | PDCP_Config__drb__discardTimer__ms200 => 9
  | PDCP_Config__drb__discardTimer__ms250 => 10
  | PDCP_Config__drb__discardTimer__ms300 => 11
  | PDCP_Config__drb__discardTimer__ms500 => 12
  | PDCP_Config__drb__discardTimer__ms750 => 13
  | PDCP_Config__drb__discardTimer__ms1500 => 14
  | PDCP_Config__drb__discardTimer__infinity => 15
  end.
Definition PDCP_Config__drb__discardTimer__F2 n :=
  match n with
  | 0 => PDCP_Config__drb__discardTimer__ms10
  | 1 => PDCP_Config__drb__discardTimer__ms20
  | 2 => PDCP_Config__drb__discardTimer__ms30
  | 3 => PDCP_Config__drb__discardTimer__ms40
  | 4 => PDCP_Config__drb__discardTimer__ms50
  | 5 => PDCP_Config__drb__discardTimer__ms60
  | 6 => PDCP_Config__drb__discardTimer__ms75
  | 7 => PDCP_Config__drb__discardTimer__ms100
  | 8 => PDCP_Config__drb__discardTimer__ms150
  | 9 => PDCP_Config__drb__discardTimer__ms200
  | 10 => PDCP_Config__drb__discardTimer__ms250
  | 11 => PDCP_Config__drb__discardTimer__ms300
  | 12 => PDCP_Config__drb__discardTimer__ms500
  | 13 => PDCP_Config__drb__discardTimer__ms750
  | 14 => PDCP_Config__drb__discardTimer__ms1500
  | 15 => PDCP_Config__drb__discardTimer__infinity
  | _ => PDCP_Config__drb__discardTimer__ms10
  end.
Lemma PDCP_Config__drb__discardTimer__F1F2 : forall x : PDCP_Config__drb__discardTimer__Type, (PDCP_Config__drb__discardTimer__F1 x <= 15) /\ PDCP_Config__drb__discardTimer__F2 (PDCP_Config__drb__discardTimer__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__drb__discardTimer__F2F1 : forall (y : nat) (H : y <= 15), PDCP_Config__drb__discardTimer__F1 (PDCP_Config__drb__discardTimer__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Config__drb__pdcp_SN_SizeUL__Type : Set :=
 | PDCP_Config__drb__pdcp_SN_SizeUL__len12bits
 | PDCP_Config__drb__pdcp_SN_SizeUL__len18bits
.
Definition PDCP_Config__drb__pdcp_SN_SizeUL__cond := (fun (_ : PDCP_Config__drb__pdcp_SN_SizeUL__Type) => True).
Lemma PDCP_Config__drb__pdcp_SN_SizeUL__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__drb__pdcp_SN_SizeUL__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDCP_Config__drb__pdcp_SN_SizeUL__nat__helper.

Definition PDCP_Config__drb__pdcp_SN_SizeUL__F1 t :=
  match t with
  | PDCP_Config__drb__pdcp_SN_SizeUL__len12bits => 0
  | PDCP_Config__drb__pdcp_SN_SizeUL__len18bits => 1
  end.
Definition PDCP_Config__drb__pdcp_SN_SizeUL__F2 n :=
  match n with
  | 0 => PDCP_Config__drb__pdcp_SN_SizeUL__len12bits
  | 1 => PDCP_Config__drb__pdcp_SN_SizeUL__len18bits
  | _ => PDCP_Config__drb__pdcp_SN_SizeUL__len12bits
  end.
Lemma PDCP_Config__drb__pdcp_SN_SizeUL__F1F2 : forall x : PDCP_Config__drb__pdcp_SN_SizeUL__Type, (PDCP_Config__drb__pdcp_SN_SizeUL__F1 x <= 1) /\ PDCP_Config__drb__pdcp_SN_SizeUL__F2 (PDCP_Config__drb__pdcp_SN_SizeUL__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__drb__pdcp_SN_SizeUL__F2F1 : forall (y : nat) (H : y <= 1), PDCP_Config__drb__pdcp_SN_SizeUL__F1 (PDCP_Config__drb__pdcp_SN_SizeUL__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Config__drb__pdcp_SN_SizeDL__Type : Set :=
 | PDCP_Config__drb__pdcp_SN_SizeDL__len12bits
 | PDCP_Config__drb__pdcp_SN_SizeDL__len18bits
.
Definition PDCP_Config__drb__pdcp_SN_SizeDL__cond := (fun (_ : PDCP_Config__drb__pdcp_SN_SizeDL__Type) => True).
Lemma PDCP_Config__drb__pdcp_SN_SizeDL__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__drb__pdcp_SN_SizeDL__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDCP_Config__drb__pdcp_SN_SizeDL__nat__helper.

Definition PDCP_Config__drb__pdcp_SN_SizeDL__F1 t :=
  match t with
  | PDCP_Config__drb__pdcp_SN_SizeDL__len12bits => 0
  | PDCP_Config__drb__pdcp_SN_SizeDL__len18bits => 1
  end.
Definition PDCP_Config__drb__pdcp_SN_SizeDL__F2 n :=
  match n with
  | 0 => PDCP_Config__drb__pdcp_SN_SizeDL__len12bits
  | 1 => PDCP_Config__drb__pdcp_SN_SizeDL__len18bits
  | _ => PDCP_Config__drb__pdcp_SN_SizeDL__len12bits
  end.
Lemma PDCP_Config__drb__pdcp_SN_SizeDL__F1F2 : forall x : PDCP_Config__drb__pdcp_SN_SizeDL__Type, (PDCP_Config__drb__pdcp_SN_SizeDL__F1 x <= 1) /\ PDCP_Config__drb__pdcp_SN_SizeDL__F2 (PDCP_Config__drb__pdcp_SN_SizeDL__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__drb__pdcp_SN_SizeDL__F2F1 : forall (y : nat) (H : y <= 1), PDCP_Config__drb__pdcp_SN_SizeDL__F1 (PDCP_Config__drb__pdcp_SN_SizeDL__F2 y) = y. enum_solve H y. Qed.

Lemma PDCP_Config__drb__headerCompression__root__rohc__maxCID__helper1 : (1 <= 16383)%Z.  lia. Qed.
Lemma PDCP_Config__drb__headerCompression__root__rohc__maxCID__helper2 : to_bit_sz (Z.to_nat (16383 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16383 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCP_Config__drb__headerCompression__root__rohc__maxCID__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCP_Config__drb__headerCompression__root__rohc__maxCID__Type := Z.
Definition PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond := (fun z => (1 <= z <= 16383)%Z).
Transparent PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond.
Lemma PDCP_Config__drb__headerCompression__root__rohc__maxCID__dft_helper : PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond 15. unfold PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond. lia. Qed.
Opaque PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond.
Record PDCP_Config__drb__headerCompression__root__rohc__profiles__Type : Set :=
  make__PDCP_Config__drb__headerCompression__root__rohc__profiles__Type {
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0001 : bool ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0002 : bool ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0003 : bool ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0004 : bool ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0006 : bool ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0101 : bool ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0102 : bool ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0103 : bool ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0104 : bool ;
}.
Definition PDCP_Config__drb__headerCompression__root__rohc__profiles__list := (
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
Definition PDCP_Config__drb__headerCompression__root__rohc__profiles__cond z := 
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0001 z) /\
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0002 z) /\
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0003 z) /\
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0004 z) /\
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0006 z) /\
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0101 z) /\
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0102 z) /\
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0103 z) /\
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0104 z) /\
  True.

Inductive PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Type : Set :=
 | PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__true
.
Definition PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__cond := (fun (_ : PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Type) => True).
Lemma PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__nat__helper.

Definition PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F1 t :=
  match t with
  | PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__true => 0
  end.
Definition PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F2 n :=
  match n with
  | 0 => PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__true
  | _ => PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__true
  end.
Lemma PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F1F2 : forall x : PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Type, (PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F1 x <= 0) /\ PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F2 (PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F1 (PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F2 y) = y. enum_solve H y. Qed.

Record PDCP_Config__drb__headerCompression__root__rohc__Type : Set :=
  make__PDCP_Config__drb__headerCompression__root__rohc__Type {
    PDCP_Config__drb__headerCompression__root__rohc__maxCID : Z ;
    PDCP_Config__drb__headerCompression__root__rohc__profiles : PDCP_Config__drb__headerCompression__root__rohc__profiles__Type ;
    PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC : option PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Type ;
}.
Definition PDCP_Config__drb__headerCompression__root__rohc__list := (
 Dft Z PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond 15%Z PDCP_Config__drb__headerCompression__root__rohc__maxCID__dft_helper Z.eq_dec ::
 Nor PDCP_Config__drb__headerCompression__root__rohc__profiles__Type PDCP_Config__drb__headerCompression__root__rohc__profiles__cond ::
 Opt PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Type PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__cond ::
 nil).
Definition PDCP_Config__drb__headerCompression__root__rohc__cond z := 
  PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond (PDCP_Config__drb__headerCompression__root__rohc__maxCID z) /\
  PDCP_Config__drb__headerCompression__root__rohc__profiles__cond (PDCP_Config__drb__headerCompression__root__rohc__profiles z) /\
  opt_cond PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__cond (PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC z) /\
  True.

Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__helper1 : (1 <= 16383)%Z.  lia. Qed.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__helper2 : to_bit_sz (Z.to_nat (16383 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16383 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__Type := Z.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond := (fun z => (1 <= z <= 16383)%Z).
Transparent PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__dft_helper : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond 15. unfold PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond. lia. Qed.
Opaque PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond.
Record PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Type : Set :=
  make__PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Type {
    PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__profile0x0006 : bool ;
}.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list := (
 Nor bool (fun _ => True) ::
 nil).
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond z := 
  (fun _ => True) (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__profile0x0006 z) /\
  True.

Inductive PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Type : Set :=
 | PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__true
.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__cond := (fun (_ : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Type) => True).
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__nat__helper.

Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F1 t :=
  match t with
  | PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__true => 0
  end.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F2 n :=
  match n with
  | 0 => PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__true
  | _ => PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__true
  end.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F1F2 : forall x : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Type, (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F1 x <= 0) /\ PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F2 (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F1 (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F2 y) = y. enum_solve H y. Qed.

Record PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type : Set :=
  make__PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type {
    PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID : Z ;
    PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Type ;
    PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC : option PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Type ;
}.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list := (
 Dft Z PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond 15%Z PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__dft_helper Z.eq_dec ::
 Nor PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond ::
 Opt PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__cond ::
 nil).
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond z := 
  PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID z) /\
  PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles z) /\
  opt_cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__cond (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC z) /\
  True.


Inductive PDCP_Config__drb__headerCompression__root__Type : Set :=
  | PDCP_Config__drb__headerCompression__root__notUsed : unit -> PDCP_Config__drb__headerCompression__root__Type
  | PDCP_Config__drb__headerCompression__root__rohc : PDCP_Config__drb__headerCompression__root__rohc__Type -> PDCP_Config__drb__headerCompression__root__Type
  | PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type -> PDCP_Config__drb__headerCompression__root__Type
.
Definition PDCP_Config__drb__headerCompression__root__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons PDCP_Config__drb__headerCompression__root__rohc__Type PDCP_Config__drb__headerCompression__root__rohc__cond ::
typ_cons PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond ::
 nil).
Definition PDCP_Config__drb__headerCompression__root__cond (c : PDCP_Config__drb__headerCompression__root__Type) := 
  match c with
  | PDCP_Config__drb__headerCompression__root__notUsed t => (fun _ => True) t 
  | PDCP_Config__drb__headerCompression__root__rohc t => PDCP_Config__drb__headerCompression__root__rohc__cond t 
  | PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC t => PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond t 
  end.

Lemma PDCP_Config__drb__headerCompression__root__len_helper1 : to_bit_sz (length PDCP_Config__drb__headerCompression__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDCP_Config__drb__headerCompression__root__len_helper2 : 2 <= length2 PDCP_Config__drb__headerCompression__root__list.
 simpl. lia. Qed.

Definition PDCP_Config__drb__headerCompression__ext__Type : Set := Empty_set.
Definition PDCP_Config__drb__headerCompression__ext__cond (c : PDCP_Config__drb__headerCompression__ext__Type) := True.
Definition PDCP_Config__drb__headerCompression__Type : Set := PDCP_Config__drb__headerCompression__root__Type + PDCP_Config__drb__headerCompression__ext__Type.
Definition PDCP_Config__drb__headerCompression__cond :=
  sum_cond PDCP_Config__drb__headerCompression__root__cond PDCP_Config__drb__headerCompression__ext__cond.
Inductive PDCP_Config__drb__integrityProtection__Type : Set :=
 | PDCP_Config__drb__integrityProtection__enabled
.
Definition PDCP_Config__drb__integrityProtection__cond := (fun (_ : PDCP_Config__drb__integrityProtection__Type) => True).
Lemma PDCP_Config__drb__integrityProtection__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__drb__integrityProtection__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Config__drb__integrityProtection__nat__helper.

Definition PDCP_Config__drb__integrityProtection__F1 t :=
  match t with
  | PDCP_Config__drb__integrityProtection__enabled => 0
  end.
Definition PDCP_Config__drb__integrityProtection__F2 n :=
  match n with
  | 0 => PDCP_Config__drb__integrityProtection__enabled
  | _ => PDCP_Config__drb__integrityProtection__enabled
  end.
Lemma PDCP_Config__drb__integrityProtection__F1F2 : forall x : PDCP_Config__drb__integrityProtection__Type, (PDCP_Config__drb__integrityProtection__F1 x <= 0) /\ PDCP_Config__drb__integrityProtection__F2 (PDCP_Config__drb__integrityProtection__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__drb__integrityProtection__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Config__drb__integrityProtection__F1 (PDCP_Config__drb__integrityProtection__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Config__drb__statusReportRequired__Type : Set :=
 | PDCP_Config__drb__statusReportRequired__true
.
Definition PDCP_Config__drb__statusReportRequired__cond := (fun (_ : PDCP_Config__drb__statusReportRequired__Type) => True).
Lemma PDCP_Config__drb__statusReportRequired__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__drb__statusReportRequired__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Config__drb__statusReportRequired__nat__helper.

Definition PDCP_Config__drb__statusReportRequired__F1 t :=
  match t with
  | PDCP_Config__drb__statusReportRequired__true => 0
  end.
Definition PDCP_Config__drb__statusReportRequired__F2 n :=
  match n with
  | 0 => PDCP_Config__drb__statusReportRequired__true
  | _ => PDCP_Config__drb__statusReportRequired__true
  end.
Lemma PDCP_Config__drb__statusReportRequired__F1F2 : forall x : PDCP_Config__drb__statusReportRequired__Type, (PDCP_Config__drb__statusReportRequired__F1 x <= 0) /\ PDCP_Config__drb__statusReportRequired__F2 (PDCP_Config__drb__statusReportRequired__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__drb__statusReportRequired__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Config__drb__statusReportRequired__F1 (PDCP_Config__drb__statusReportRequired__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Config__drb__outOfOrderDelivery__Type : Set :=
 | PDCP_Config__drb__outOfOrderDelivery__true
.
Definition PDCP_Config__drb__outOfOrderDelivery__cond := (fun (_ : PDCP_Config__drb__outOfOrderDelivery__Type) => True).
Lemma PDCP_Config__drb__outOfOrderDelivery__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__drb__outOfOrderDelivery__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Config__drb__outOfOrderDelivery__nat__helper.

Definition PDCP_Config__drb__outOfOrderDelivery__F1 t :=
  match t with
  | PDCP_Config__drb__outOfOrderDelivery__true => 0
  end.
Definition PDCP_Config__drb__outOfOrderDelivery__F2 n :=
  match n with
  | 0 => PDCP_Config__drb__outOfOrderDelivery__true
  | _ => PDCP_Config__drb__outOfOrderDelivery__true
  end.
Lemma PDCP_Config__drb__outOfOrderDelivery__F1F2 : forall x : PDCP_Config__drb__outOfOrderDelivery__Type, (PDCP_Config__drb__outOfOrderDelivery__F1 x <= 0) /\ PDCP_Config__drb__outOfOrderDelivery__F2 (PDCP_Config__drb__outOfOrderDelivery__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__drb__outOfOrderDelivery__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Config__drb__outOfOrderDelivery__F1 (PDCP_Config__drb__outOfOrderDelivery__F2 y) = y. enum_solve H y. Qed.

Record PDCP_Config__drb__Type : Set :=
  make__PDCP_Config__drb__Type {
    PDCP_Config__drb__discardTimer : option PDCP_Config__drb__discardTimer__Type ;
    PDCP_Config__drb__pdcp_SN_SizeUL : option PDCP_Config__drb__pdcp_SN_SizeUL__Type ;
    PDCP_Config__drb__pdcp_SN_SizeDL : option PDCP_Config__drb__pdcp_SN_SizeDL__Type ;
    PDCP_Config__drb__headerCompression : PDCP_Config__drb__headerCompression__Type ;
    PDCP_Config__drb__integrityProtection : option PDCP_Config__drb__integrityProtection__Type ;
    PDCP_Config__drb__statusReportRequired : option PDCP_Config__drb__statusReportRequired__Type ;
    PDCP_Config__drb__outOfOrderDelivery : option PDCP_Config__drb__outOfOrderDelivery__Type ;
}.
Definition PDCP_Config__drb__list := (
 Opt PDCP_Config__drb__discardTimer__Type PDCP_Config__drb__discardTimer__cond ::
 Opt PDCP_Config__drb__pdcp_SN_SizeUL__Type PDCP_Config__drb__pdcp_SN_SizeUL__cond ::
 Opt PDCP_Config__drb__pdcp_SN_SizeDL__Type PDCP_Config__drb__pdcp_SN_SizeDL__cond ::
 Nor PDCP_Config__drb__headerCompression__Type PDCP_Config__drb__headerCompression__cond ::
 Opt PDCP_Config__drb__integrityProtection__Type PDCP_Config__drb__integrityProtection__cond ::
 Opt PDCP_Config__drb__statusReportRequired__Type PDCP_Config__drb__statusReportRequired__cond ::
 Opt PDCP_Config__drb__outOfOrderDelivery__Type PDCP_Config__drb__outOfOrderDelivery__cond ::
 nil).
Definition PDCP_Config__drb__cond z := 
  opt_cond PDCP_Config__drb__discardTimer__cond (PDCP_Config__drb__discardTimer z) /\
  opt_cond PDCP_Config__drb__pdcp_SN_SizeUL__cond (PDCP_Config__drb__pdcp_SN_SizeUL z) /\
  opt_cond PDCP_Config__drb__pdcp_SN_SizeDL__cond (PDCP_Config__drb__pdcp_SN_SizeDL z) /\
  PDCP_Config__drb__headerCompression__cond (PDCP_Config__drb__headerCompression z) /\
  opt_cond PDCP_Config__drb__integrityProtection__cond (PDCP_Config__drb__integrityProtection z) /\
  opt_cond PDCP_Config__drb__statusReportRequired__cond (PDCP_Config__drb__statusReportRequired z) /\
  opt_cond PDCP_Config__drb__outOfOrderDelivery__cond (PDCP_Config__drb__outOfOrderDelivery z) /\
  True.

Require Import NR.CellGroupId.

Opaque CellGroupId__cond CellGroupId__Format.

Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Record PDCP_Config__moreThanOneRLC__primaryPath__Type : Set :=
  make__PDCP_Config__moreThanOneRLC__primaryPath__Type {
    PDCP_Config__moreThanOneRLC__primaryPath__cellGroup : option CellGroupId__Type ;
    PDCP_Config__moreThanOneRLC__primaryPath__logicalChannel : option LogicalChannelIdentity__Type ;
}.
Definition PDCP_Config__moreThanOneRLC__primaryPath__list := (
 Opt CellGroupId__Type CellGroupId__cond ::
 Opt LogicalChannelIdentity__Type LogicalChannelIdentity__cond ::
 nil).
Definition PDCP_Config__moreThanOneRLC__primaryPath__cond z := 
  opt_cond CellGroupId__cond (PDCP_Config__moreThanOneRLC__primaryPath__cellGroup z) /\
  opt_cond LogicalChannelIdentity__cond (PDCP_Config__moreThanOneRLC__primaryPath__logicalChannel z) /\
  True.

Require Import NR.UL_DataSplitThreshold.

Opaque UL_DataSplitThreshold__cond UL_DataSplitThreshold__Format.

Record PDCP_Config__moreThanOneRLC__Type : Set :=
  make__PDCP_Config__moreThanOneRLC__Type {
    PDCP_Config__moreThanOneRLC__primaryPath : PDCP_Config__moreThanOneRLC__primaryPath__Type ;
    PDCP_Config__moreThanOneRLC__ul_DataSplitThreshold : option UL_DataSplitThreshold__Type ;
    PDCP_Config__moreThanOneRLC__pdcp_Duplication : option bool ;
}.
Definition PDCP_Config__moreThanOneRLC__list := (
 Nor PDCP_Config__moreThanOneRLC__primaryPath__Type PDCP_Config__moreThanOneRLC__primaryPath__cond ::
 Opt UL_DataSplitThreshold__Type UL_DataSplitThreshold__cond ::
 Opt bool (fun _ => True) ::
 nil).
Definition PDCP_Config__moreThanOneRLC__cond z := 
  PDCP_Config__moreThanOneRLC__primaryPath__cond (PDCP_Config__moreThanOneRLC__primaryPath z) /\
  opt_cond UL_DataSplitThreshold__cond (PDCP_Config__moreThanOneRLC__ul_DataSplitThreshold z) /\
  opt_cond (fun _ => True) (PDCP_Config__moreThanOneRLC__pdcp_Duplication z) /\
  True.

Inductive PDCP_Config__t_Reordering__Type : Set :=
 | PDCP_Config__t_Reordering__ms0
 | PDCP_Config__t_Reordering__ms1
 | PDCP_Config__t_Reordering__ms2
 | PDCP_Config__t_Reordering__ms4
 | PDCP_Config__t_Reordering__ms5
 | PDCP_Config__t_Reordering__ms8
 | PDCP_Config__t_Reordering__ms10
 | PDCP_Config__t_Reordering__ms15
 | PDCP_Config__t_Reordering__ms20
 | PDCP_Config__t_Reordering__ms30
 | PDCP_Config__t_Reordering__ms40
 | PDCP_Config__t_Reordering__ms50
 | PDCP_Config__t_Reordering__ms60
 | PDCP_Config__t_Reordering__ms80
 | PDCP_Config__t_Reordering__ms100
 | PDCP_Config__t_Reordering__ms120
 | PDCP_Config__t_Reordering__ms140
 | PDCP_Config__t_Reordering__ms160
 | PDCP_Config__t_Reordering__ms180
 | PDCP_Config__t_Reordering__ms200
 | PDCP_Config__t_Reordering__ms220
 | PDCP_Config__t_Reordering__ms240
 | PDCP_Config__t_Reordering__ms260
 | PDCP_Config__t_Reordering__ms280
 | PDCP_Config__t_Reordering__ms300
 | PDCP_Config__t_Reordering__ms500
 | PDCP_Config__t_Reordering__ms750
 | PDCP_Config__t_Reordering__ms1000
 | PDCP_Config__t_Reordering__ms1250
 | PDCP_Config__t_Reordering__ms1500
 | PDCP_Config__t_Reordering__ms1750
 | PDCP_Config__t_Reordering__ms2000
 | PDCP_Config__t_Reordering__ms2250
 | PDCP_Config__t_Reordering__ms2500
 | PDCP_Config__t_Reordering__ms2750
 | PDCP_Config__t_Reordering__ms3000
 | PDCP_Config__t_Reordering__spare28
 | PDCP_Config__t_Reordering__spare27
 | PDCP_Config__t_Reordering__spare26
 | PDCP_Config__t_Reordering__spare25
 | PDCP_Config__t_Reordering__spare24
 | PDCP_Config__t_Reordering__spare23
 | PDCP_Config__t_Reordering__spare22
 | PDCP_Config__t_Reordering__spare21
 | PDCP_Config__t_Reordering__spare20
 | PDCP_Config__t_Reordering__spare19
 | PDCP_Config__t_Reordering__spare18
 | PDCP_Config__t_Reordering__spare17
 | PDCP_Config__t_Reordering__spare16
 | PDCP_Config__t_Reordering__spare15
 | PDCP_Config__t_Reordering__spare14
 | PDCP_Config__t_Reordering__spare13
 | PDCP_Config__t_Reordering__spare12
 | PDCP_Config__t_Reordering__spare11
 | PDCP_Config__t_Reordering__spare10
 | PDCP_Config__t_Reordering__spare09
 | PDCP_Config__t_Reordering__spare08
 | PDCP_Config__t_Reordering__spare07
 | PDCP_Config__t_Reordering__spare06
 | PDCP_Config__t_Reordering__spare05
 | PDCP_Config__t_Reordering__spare04
 | PDCP_Config__t_Reordering__spare03
 | PDCP_Config__t_Reordering__spare02
 | PDCP_Config__t_Reordering__spare01
.
Definition PDCP_Config__t_Reordering__cond := (fun (_ : PDCP_Config__t_Reordering__Type) => True).
Lemma PDCP_Config__t_Reordering__nat__helper : to_bit_sz 63 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__t_Reordering__nat__Format : T_Format nat (fun z => (z <= 63)) :=
  nat_enum_format 63 PDCP_Config__t_Reordering__nat__helper.

Definition PDCP_Config__t_Reordering__F1 t :=
  match t with
  | PDCP_Config__t_Reordering__ms0 => 0
  | PDCP_Config__t_Reordering__ms1 => 1
  | PDCP_Config__t_Reordering__ms2 => 2
  | PDCP_Config__t_Reordering__ms4 => 3
  | PDCP_Config__t_Reordering__ms5 => 4
  | PDCP_Config__t_Reordering__ms8 => 5
  | PDCP_Config__t_Reordering__ms10 => 6
  | PDCP_Config__t_Reordering__ms15 => 7
  | PDCP_Config__t_Reordering__ms20 => 8
  | PDCP_Config__t_Reordering__ms30 => 9
  | PDCP_Config__t_Reordering__ms40 => 10
  | PDCP_Config__t_Reordering__ms50 => 11
  | PDCP_Config__t_Reordering__ms60 => 12
  | PDCP_Config__t_Reordering__ms80 => 13
  | PDCP_Config__t_Reordering__ms100 => 14
  | PDCP_Config__t_Reordering__ms120 => 15
  | PDCP_Config__t_Reordering__ms140 => 16
  | PDCP_Config__t_Reordering__ms160 => 17
  | PDCP_Config__t_Reordering__ms180 => 18
  | PDCP_Config__t_Reordering__ms200 => 19
  | PDCP_Config__t_Reordering__ms220 => 20
  | PDCP_Config__t_Reordering__ms240 => 21
  | PDCP_Config__t_Reordering__ms260 => 22
  | PDCP_Config__t_Reordering__ms280 => 23
  | PDCP_Config__t_Reordering__ms300 => 24
  | PDCP_Config__t_Reordering__ms500 => 25
  | PDCP_Config__t_Reordering__ms750 => 26
  | PDCP_Config__t_Reordering__ms1000 => 27
  | PDCP_Config__t_Reordering__ms1250 => 28
  | PDCP_Config__t_Reordering__ms1500 => 29
  | PDCP_Config__t_Reordering__ms1750 => 30
  | PDCP_Config__t_Reordering__ms2000 => 31
  | PDCP_Config__t_Reordering__ms2250 => 32
  | PDCP_Config__t_Reordering__ms2500 => 33
  | PDCP_Config__t_Reordering__ms2750 => 34
  | PDCP_Config__t_Reordering__ms3000 => 35
  | PDCP_Config__t_Reordering__spare28 => 36
  | PDCP_Config__t_Reordering__spare27 => 37
  | PDCP_Config__t_Reordering__spare26 => 38
  | PDCP_Config__t_Reordering__spare25 => 39
  | PDCP_Config__t_Reordering__spare24 => 40
  | PDCP_Config__t_Reordering__spare23 => 41
  | PDCP_Config__t_Reordering__spare22 => 42
  | PDCP_Config__t_Reordering__spare21 => 43
  | PDCP_Config__t_Reordering__spare20 => 44
  | PDCP_Config__t_Reordering__spare19 => 45
  | PDCP_Config__t_Reordering__spare18 => 46
  | PDCP_Config__t_Reordering__spare17 => 47
  | PDCP_Config__t_Reordering__spare16 => 48
  | PDCP_Config__t_Reordering__spare15 => 49
  | PDCP_Config__t_Reordering__spare14 => 50
  | PDCP_Config__t_Reordering__spare13 => 51
  | PDCP_Config__t_Reordering__spare12 => 52
  | PDCP_Config__t_Reordering__spare11 => 53
  | PDCP_Config__t_Reordering__spare10 => 54
  | PDCP_Config__t_Reordering__spare09 => 55
  | PDCP_Config__t_Reordering__spare08 => 56
  | PDCP_Config__t_Reordering__spare07 => 57
  | PDCP_Config__t_Reordering__spare06 => 58
  | PDCP_Config__t_Reordering__spare05 => 59
  | PDCP_Config__t_Reordering__spare04 => 60
  | PDCP_Config__t_Reordering__spare03 => 61
  | PDCP_Config__t_Reordering__spare02 => 62
  | PDCP_Config__t_Reordering__spare01 => 63
  end.
Definition PDCP_Config__t_Reordering__F2 n :=
  match n with
  | 0 => PDCP_Config__t_Reordering__ms0
  | 1 => PDCP_Config__t_Reordering__ms1
  | 2 => PDCP_Config__t_Reordering__ms2
  | 3 => PDCP_Config__t_Reordering__ms4
  | 4 => PDCP_Config__t_Reordering__ms5
  | 5 => PDCP_Config__t_Reordering__ms8
  | 6 => PDCP_Config__t_Reordering__ms10
  | 7 => PDCP_Config__t_Reordering__ms15
  | 8 => PDCP_Config__t_Reordering__ms20
  | 9 => PDCP_Config__t_Reordering__ms30
  | 10 => PDCP_Config__t_Reordering__ms40
  | 11 => PDCP_Config__t_Reordering__ms50
  | 12 => PDCP_Config__t_Reordering__ms60
  | 13 => PDCP_Config__t_Reordering__ms80
  | 14 => PDCP_Config__t_Reordering__ms100
  | 15 => PDCP_Config__t_Reordering__ms120
  | 16 => PDCP_Config__t_Reordering__ms140
  | 17 => PDCP_Config__t_Reordering__ms160
  | 18 => PDCP_Config__t_Reordering__ms180
  | 19 => PDCP_Config__t_Reordering__ms200
  | 20 => PDCP_Config__t_Reordering__ms220
  | 21 => PDCP_Config__t_Reordering__ms240
  | 22 => PDCP_Config__t_Reordering__ms260
  | 23 => PDCP_Config__t_Reordering__ms280
  | 24 => PDCP_Config__t_Reordering__ms300
  | 25 => PDCP_Config__t_Reordering__ms500
  | 26 => PDCP_Config__t_Reordering__ms750
  | 27 => PDCP_Config__t_Reordering__ms1000
  | 28 => PDCP_Config__t_Reordering__ms1250
  | 29 => PDCP_Config__t_Reordering__ms1500
  | 30 => PDCP_Config__t_Reordering__ms1750
  | 31 => PDCP_Config__t_Reordering__ms2000
  | 32 => PDCP_Config__t_Reordering__ms2250
  | 33 => PDCP_Config__t_Reordering__ms2500
  | 34 => PDCP_Config__t_Reordering__ms2750
  | 35 => PDCP_Config__t_Reordering__ms3000
  | 36 => PDCP_Config__t_Reordering__spare28
  | 37 => PDCP_Config__t_Reordering__spare27
  | 38 => PDCP_Config__t_Reordering__spare26
  | 39 => PDCP_Config__t_Reordering__spare25
  | 40 => PDCP_Config__t_Reordering__spare24
  | 41 => PDCP_Config__t_Reordering__spare23
  | 42 => PDCP_Config__t_Reordering__spare22
  | 43 => PDCP_Config__t_Reordering__spare21
  | 44 => PDCP_Config__t_Reordering__spare20
  | 45 => PDCP_Config__t_Reordering__spare19
  | 46 => PDCP_Config__t_Reordering__spare18
  | 47 => PDCP_Config__t_Reordering__spare17
  | 48 => PDCP_Config__t_Reordering__spare16
  | 49 => PDCP_Config__t_Reordering__spare15
  | 50 => PDCP_Config__t_Reordering__spare14
  | 51 => PDCP_Config__t_Reordering__spare13
  | 52 => PDCP_Config__t_Reordering__spare12
  | 53 => PDCP_Config__t_Reordering__spare11
  | 54 => PDCP_Config__t_Reordering__spare10
  | 55 => PDCP_Config__t_Reordering__spare09
  | 56 => PDCP_Config__t_Reordering__spare08
  | 57 => PDCP_Config__t_Reordering__spare07
  | 58 => PDCP_Config__t_Reordering__spare06
  | 59 => PDCP_Config__t_Reordering__spare05
  | 60 => PDCP_Config__t_Reordering__spare04
  | 61 => PDCP_Config__t_Reordering__spare03
  | 62 => PDCP_Config__t_Reordering__spare02
  | 63 => PDCP_Config__t_Reordering__spare01
  | _ => PDCP_Config__t_Reordering__ms0
  end.
Lemma PDCP_Config__t_Reordering__F1F2 : forall x : PDCP_Config__t_Reordering__Type, (PDCP_Config__t_Reordering__F1 x <= 63) /\ PDCP_Config__t_Reordering__F2 (PDCP_Config__t_Reordering__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__t_Reordering__F2F1 : forall (y : nat) (H : y <= 63), PDCP_Config__t_Reordering__F1 (PDCP_Config__t_Reordering__F2 y) = y. enum_solve H y. Qed.

Inductive PDCP_Config__ext0O__cipheringDisabled__Type : Set :=
 | PDCP_Config__ext0O__cipheringDisabled__true
.
Definition PDCP_Config__ext0O__cipheringDisabled__cond := (fun (_ : PDCP_Config__ext0O__cipheringDisabled__Type) => True).
Lemma PDCP_Config__ext0O__cipheringDisabled__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__ext0O__cipheringDisabled__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Config__ext0O__cipheringDisabled__nat__helper.

Definition PDCP_Config__ext0O__cipheringDisabled__F1 t :=
  match t with
  | PDCP_Config__ext0O__cipheringDisabled__true => 0
  end.
Definition PDCP_Config__ext0O__cipheringDisabled__F2 n :=
  match n with
  | 0 => PDCP_Config__ext0O__cipheringDisabled__true
  | _ => PDCP_Config__ext0O__cipheringDisabled__true
  end.
Lemma PDCP_Config__ext0O__cipheringDisabled__F1F2 : forall x : PDCP_Config__ext0O__cipheringDisabled__Type, (PDCP_Config__ext0O__cipheringDisabled__F1 x <= 0) /\ PDCP_Config__ext0O__cipheringDisabled__F2 (PDCP_Config__ext0O__cipheringDisabled__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__ext0O__cipheringDisabled__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Config__ext0O__cipheringDisabled__F1 (PDCP_Config__ext0O__cipheringDisabled__F2 y) = y. enum_solve H y. Qed.

Record PDCP_Config__ext0O__Type : Set :=
  make__PDCP_Config__ext0O__Type {
    PDCP_Config__ext0O__cipheringDisabled : option PDCP_Config__ext0O__cipheringDisabled__Type ;
}.
Definition PDCP_Config__ext0O__list := (
 Opt PDCP_Config__ext0O__cipheringDisabled__Type PDCP_Config__ext0O__cipheringDisabled__cond ::
 nil).
Definition PDCP_Config__ext0O__cond z := 
  opt_cond PDCP_Config__ext0O__cipheringDisabled__cond (PDCP_Config__ext0O__cipheringDisabled z) /\
  True.

Definition PDCP_Config__ext0__Type := PDCP_Config__ext0O__Type.
Definition PDCP_Config__ext0__cond := PDCP_Config__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.DiscardTimerExt_r16.
Definition PDCP_Config__ext1O__discardTimerExt_r16__Type := SetupRelease__Type DiscardTimerExt_r16__Type.
Definition PDCP_Config__ext1O__discardTimerExt_r16__cond := SetupRelease__cond _ DiscardTimerExt_r16__cond.
Definition PDCP_Config__ext1O__discardTimerExt_r16__Format : T_Format PDCP_Config__ext1O__discardTimerExt_r16__Type PDCP_Config__ext1O__discardTimerExt_r16__cond := SetupRelease__Format _ _ DiscardTimerExt_r16__Format.
Opaque PDCP_Config__ext1O__discardTimerExt_r16__cond PDCP_Config__ext1O__discardTimerExt_r16__Format.

Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__Type := list bool.

Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__cond (z : PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__Type) := (list_and (fun _ => True) z) /\ (length z = Z.to_nat 3).

Record PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Type : Set :=
  make__PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Type {
    PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__splitSecondaryPath_r16 : option LogicalChannelIdentity__Type ;
    PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16 : option PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__Type ;
}.
Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list := (
 Opt LogicalChannelIdentity__Type LogicalChannelIdentity__cond ::
 Opt PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__Type PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__cond ::
 nil).
Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond z := 
  opt_cond LogicalChannelIdentity__cond (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__splitSecondaryPath_r16 z) /\
  opt_cond PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__cond (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16 z) /\
  True.

Require Import NR.SetupRelease.
Require Import NR.EthernetHeaderCompression_r16.
Definition PDCP_Config__ext1O__ethernetHeaderCompression_r16__Type := SetupRelease__Type EthernetHeaderCompression_r16__Type.
Definition PDCP_Config__ext1O__ethernetHeaderCompression_r16__cond := SetupRelease__cond _ EthernetHeaderCompression_r16__cond.
Definition PDCP_Config__ext1O__ethernetHeaderCompression_r16__Format : T_Format PDCP_Config__ext1O__ethernetHeaderCompression_r16__Type PDCP_Config__ext1O__ethernetHeaderCompression_r16__cond := SetupRelease__Format _ _ EthernetHeaderCompression_r16__Format.
Opaque PDCP_Config__ext1O__ethernetHeaderCompression_r16__cond PDCP_Config__ext1O__ethernetHeaderCompression_r16__Format.

Record PDCP_Config__ext1O__Type : Set :=
  make__PDCP_Config__ext1O__Type {
    PDCP_Config__ext1O__discardTimerExt_r16 : option PDCP_Config__ext1O__discardTimerExt_r16__Type ;
    PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16 : option PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Type ;
    PDCP_Config__ext1O__ethernetHeaderCompression_r16 : option PDCP_Config__ext1O__ethernetHeaderCompression_r16__Type ;
}.
Definition PDCP_Config__ext1O__list := (
 Opt PDCP_Config__ext1O__discardTimerExt_r16__Type PDCP_Config__ext1O__discardTimerExt_r16__cond ::
 Opt PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Type PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond ::
 Opt PDCP_Config__ext1O__ethernetHeaderCompression_r16__Type PDCP_Config__ext1O__ethernetHeaderCompression_r16__cond ::
 nil).
Definition PDCP_Config__ext1O__cond z := 
  opt_cond PDCP_Config__ext1O__discardTimerExt_r16__cond (PDCP_Config__ext1O__discardTimerExt_r16 z) /\
  opt_cond PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16 z) /\
  opt_cond PDCP_Config__ext1O__ethernetHeaderCompression_r16__cond (PDCP_Config__ext1O__ethernetHeaderCompression_r16 z) /\
  True.

Definition PDCP_Config__ext1__Type := PDCP_Config__ext1O__Type.
Definition PDCP_Config__ext1__cond := PDCP_Config__ext1O__cond.

Inductive PDCP_Config__ext2O__survivalTimeStateSupport_r17__Type : Set :=
 | PDCP_Config__ext2O__survivalTimeStateSupport_r17__true
.
Definition PDCP_Config__ext2O__survivalTimeStateSupport_r17__cond := (fun (_ : PDCP_Config__ext2O__survivalTimeStateSupport_r17__Type) => True).
Lemma PDCP_Config__ext2O__survivalTimeStateSupport_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCP_Config__ext2O__survivalTimeStateSupport_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCP_Config__ext2O__survivalTimeStateSupport_r17__nat__helper.

Definition PDCP_Config__ext2O__survivalTimeStateSupport_r17__F1 t :=
  match t with
  | PDCP_Config__ext2O__survivalTimeStateSupport_r17__true => 0
  end.
Definition PDCP_Config__ext2O__survivalTimeStateSupport_r17__F2 n :=
  match n with
  | 0 => PDCP_Config__ext2O__survivalTimeStateSupport_r17__true
  | _ => PDCP_Config__ext2O__survivalTimeStateSupport_r17__true
  end.
Lemma PDCP_Config__ext2O__survivalTimeStateSupport_r17__F1F2 : forall x : PDCP_Config__ext2O__survivalTimeStateSupport_r17__Type, (PDCP_Config__ext2O__survivalTimeStateSupport_r17__F1 x <= 0) /\ PDCP_Config__ext2O__survivalTimeStateSupport_r17__F2 (PDCP_Config__ext2O__survivalTimeStateSupport_r17__F1 x) = x. imp_solve. Qed.
Lemma PDCP_Config__ext2O__survivalTimeStateSupport_r17__F2F1 : forall (y : nat) (H : y <= 0), PDCP_Config__ext2O__survivalTimeStateSupport_r17__F1 (PDCP_Config__ext2O__survivalTimeStateSupport_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.UplinkDataCompression_r17.
Definition PDCP_Config__ext2O__uplinkDataCompression_r17__Type := SetupRelease__Type UplinkDataCompression_r17__Type.
Definition PDCP_Config__ext2O__uplinkDataCompression_r17__cond := SetupRelease__cond _ UplinkDataCompression_r17__cond.
Definition PDCP_Config__ext2O__uplinkDataCompression_r17__Format : T_Format PDCP_Config__ext2O__uplinkDataCompression_r17__Type PDCP_Config__ext2O__uplinkDataCompression_r17__cond := SetupRelease__Format _ _ UplinkDataCompression_r17__Format.
Opaque PDCP_Config__ext2O__uplinkDataCompression_r17__cond PDCP_Config__ext2O__uplinkDataCompression_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.DiscardTimerExt2_r17.
Definition PDCP_Config__ext2O__discardTimerExt2_r17__Type := SetupRelease__Type DiscardTimerExt2_r17__Type.
Definition PDCP_Config__ext2O__discardTimerExt2_r17__cond := SetupRelease__cond _ DiscardTimerExt2_r17__cond.
Definition PDCP_Config__ext2O__discardTimerExt2_r17__Format : T_Format PDCP_Config__ext2O__discardTimerExt2_r17__Type PDCP_Config__ext2O__discardTimerExt2_r17__cond := SetupRelease__Format _ _ DiscardTimerExt2_r17__Format.
Opaque PDCP_Config__ext2O__discardTimerExt2_r17__cond PDCP_Config__ext2O__discardTimerExt2_r17__Format.

Definition PDCP_Config__ext2O__initialRX_DELIV_r17__Type := bit_string_fixed.
Definition PDCP_Config__ext2O__initialRX_DELIV_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 32 /\ bit_string_len_prop (fst z) (snd z)).
Record PDCP_Config__ext2O__Type : Set :=
  make__PDCP_Config__ext2O__Type {
    PDCP_Config__ext2O__survivalTimeStateSupport_r17 : option PDCP_Config__ext2O__survivalTimeStateSupport_r17__Type ;
    PDCP_Config__ext2O__uplinkDataCompression_r17 : option PDCP_Config__ext2O__uplinkDataCompression_r17__Type ;
    PDCP_Config__ext2O__discardTimerExt2_r17 : option PDCP_Config__ext2O__discardTimerExt2_r17__Type ;
    PDCP_Config__ext2O__initialRX_DELIV_r17 : option PDCP_Config__ext2O__initialRX_DELIV_r17__Type ;
}.
Definition PDCP_Config__ext2O__list := (
 Opt PDCP_Config__ext2O__survivalTimeStateSupport_r17__Type PDCP_Config__ext2O__survivalTimeStateSupport_r17__cond ::
 Opt PDCP_Config__ext2O__uplinkDataCompression_r17__Type PDCP_Config__ext2O__uplinkDataCompression_r17__cond ::
 Opt PDCP_Config__ext2O__discardTimerExt2_r17__Type PDCP_Config__ext2O__discardTimerExt2_r17__cond ::
 Opt PDCP_Config__ext2O__initialRX_DELIV_r17__Type PDCP_Config__ext2O__initialRX_DELIV_r17__cond ::
 nil).
Definition PDCP_Config__ext2O__cond z := 
  opt_cond PDCP_Config__ext2O__survivalTimeStateSupport_r17__cond (PDCP_Config__ext2O__survivalTimeStateSupport_r17 z) /\
  opt_cond PDCP_Config__ext2O__uplinkDataCompression_r17__cond (PDCP_Config__ext2O__uplinkDataCompression_r17 z) /\
  opt_cond PDCP_Config__ext2O__discardTimerExt2_r17__cond (PDCP_Config__ext2O__discardTimerExt2_r17 z) /\
  opt_cond PDCP_Config__ext2O__initialRX_DELIV_r17__cond (PDCP_Config__ext2O__initialRX_DELIV_r17 z) /\
  True.

Definition PDCP_Config__ext2__Type := PDCP_Config__ext2O__Type.
Definition PDCP_Config__ext2__cond := PDCP_Config__ext2O__cond.

Record PDCP_Config__Type : Set :=
  make__PDCP_Config__Type {
    PDCP_Config__drb : option PDCP_Config__drb__Type ;
    PDCP_Config__moreThanOneRLC : option PDCP_Config__moreThanOneRLC__Type ;
    PDCP_Config__t_Reordering : option PDCP_Config__t_Reordering__Type ;
    PDCP_Config__ext0 : option PDCP_Config__ext0__Type ;
    PDCP_Config__ext1 : option PDCP_Config__ext1__Type ;
    PDCP_Config__ext2 : option PDCP_Config__ext2__Type ;
}.
Definition PDCP_Config__root_list : list seq_elem := (
 Opt PDCP_Config__drb__Type PDCP_Config__drb__cond ::
 Opt PDCP_Config__moreThanOneRLC__Type PDCP_Config__moreThanOneRLC__cond ::
 Opt PDCP_Config__t_Reordering__Type PDCP_Config__t_Reordering__cond ::
 nil).
Definition PDCP_Config__ext_list : list typ := (
  typ_cons PDCP_Config__ext0__Type PDCP_Config__ext0__cond ::
  typ_cons PDCP_Config__ext1__Type PDCP_Config__ext1__cond ::
  typ_cons PDCP_Config__ext2__Type PDCP_Config__ext2__cond ::
  nil).
Definition PDCP_Config__cond (z : PDCP_Config__Type) := 
(  opt_cond PDCP_Config__drb__cond (PDCP_Config__drb z) /\
  opt_cond PDCP_Config__moreThanOneRLC__cond (PDCP_Config__moreThanOneRLC z) /\
  opt_cond PDCP_Config__t_Reordering__cond (PDCP_Config__t_Reordering z) /\
  True) /\ 
(  opt_cond PDCP_Config__ext0__cond (PDCP_Config__ext0 z) /\
  opt_cond PDCP_Config__ext1__cond (PDCP_Config__ext1 z) /\
  opt_cond PDCP_Config__ext2__cond (PDCP_Config__ext2 z) /\
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
Definition PDCP_Config__drb__discardTimer__Format : T_Format PDCP_Config__drb__discardTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__drb__discardTimer__nat__Format PDCP_Config__drb__discardTimer__F1 PDCP_Config__drb__discardTimer__F2 PDCP_Config__drb__discardTimer__F1F2 PDCP_Config__drb__discardTimer__F2F1.

Opaque PDCP_Config__drb__discardTimer__cond PDCP_Config__drb__discardTimer__Format.

Definition PDCP_Config__drb__pdcp_SN_SizeUL__Format : T_Format PDCP_Config__drb__pdcp_SN_SizeUL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__drb__pdcp_SN_SizeUL__nat__Format PDCP_Config__drb__pdcp_SN_SizeUL__F1 PDCP_Config__drb__pdcp_SN_SizeUL__F2 PDCP_Config__drb__pdcp_SN_SizeUL__F1F2 PDCP_Config__drb__pdcp_SN_SizeUL__F2F1.

Opaque PDCP_Config__drb__pdcp_SN_SizeUL__cond PDCP_Config__drb__pdcp_SN_SizeUL__Format.

Definition PDCP_Config__drb__pdcp_SN_SizeDL__Format : T_Format PDCP_Config__drb__pdcp_SN_SizeDL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__drb__pdcp_SN_SizeDL__nat__Format PDCP_Config__drb__pdcp_SN_SizeDL__F1 PDCP_Config__drb__pdcp_SN_SizeDL__F2 PDCP_Config__drb__pdcp_SN_SizeDL__F1F2 PDCP_Config__drb__pdcp_SN_SizeDL__F2F1.

Opaque PDCP_Config__drb__pdcp_SN_SizeDL__cond PDCP_Config__drb__pdcp_SN_SizeDL__Format.

Definition PDCP_Config__drb__headerCompression__root__rohc__maxCID__Format : T_Format Z PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond :=
 ranged_int_format (1) (16383) PDCP_Config__drb__headerCompression__root__rohc__maxCID__helper1 PDCP_Config__drb__headerCompression__root__rohc__maxCID__helper2.

Opaque PDCP_Config__drb__headerCompression__root__rohc__maxCID__cond PDCP_Config__drb__headerCompression__root__rohc__maxCID__Format.


Definition PDCP_Config__drb__headerCompression__root__rohc__profiles__Format_Type := Eval cbn in seq_format_prod PDCP_Config__drb__headerCompression__root__rohc__profiles__list.
Definition PDCP_Config__drb__headerCompression__root__rohc__profiles__Format_list : PDCP_Config__drb__headerCompression__root__rohc__profiles__Format_Type :=
  (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, (bool__Format, unit_format))))))))).
Definition PDCP_Config__drb__headerCompression__root__rohc__profiles__list__Format := (*Eval compute in *) seq_format PDCP_Config__drb__headerCompression__root__rohc__profiles__list PDCP_Config__drb__headerCompression__root__rohc__profiles__Format_list.
Definition PDCP_Config__drb__headerCompression__root__rohc__profiles__F1 z :=
  (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0001 z, (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0002 z, (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0003 z, (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0004 z, (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0006 z, (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0101 z, (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0102 z, (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0103 z, (PDCP_Config__drb__headerCompression__root__rohc__profiles__profile0x0104 z, tt))))))))).
Definition PDCP_Config__drb__headerCompression__root__rohc__profiles__F2 (y : seq_type PDCP_Config__drb__headerCompression__root__rohc__profiles__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _)))))))))=>
    make__PDCP_Config__drb__headerCompression__root__rohc__profiles__Type i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Lemma PDCP_Config__drb__headerCompression__root__rohc__profiles__F1F2_cond (z : PDCP_Config__drb__headerCompression__root__rohc__profiles__Type)
  : PDCP_Config__drb__headerCompression__root__rohc__profiles__cond z ->
  (seq_cond PDCP_Config__drb__headerCompression__root__rohc__profiles__list (PDCP_Config__drb__headerCompression__root__rohc__profiles__F1 z)).
intro H. unfold PDCP_Config__drb__headerCompression__root__rohc__profiles__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__drb__headerCompression__root__rohc__profiles__F1F2_cond2 (z : PDCP_Config__drb__headerCompression__root__rohc__profiles__Type)
 : PDCP_Config__drb__headerCompression__root__rohc__profiles__F2 (PDCP_Config__drb__headerCompression__root__rohc__profiles__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__drb__headerCompression__root__rohc__profiles__F2F1_cond (y : seq_type PDCP_Config__drb__headerCompression__root__rohc__profiles__list)
  : seq_cond PDCP_Config__drb__headerCompression__root__rohc__profiles__list y ->
 (PDCP_Config__drb__headerCompression__root__rohc__profiles__cond (PDCP_Config__drb__headerCompression__root__rohc__profiles__F2 y)) /\  PDCP_Config__drb__headerCompression__root__rohc__profiles__F1 (PDCP_Config__drb__headerCompression__root__rohc__profiles__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__drb__headerCompression__root__rohc__profiles__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__drb__headerCompression__root__rohc__profiles__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__drb__headerCompression__root__rohc__profiles__Format : T_Format PDCP_Config__drb__headerCompression__root__rohc__profiles__Type PDCP_Config__drb__headerCompression__root__rohc__profiles__cond :=
        proj2_format  PDCP_Config__drb__headerCompression__root__rohc__profiles__cond PDCP_Config__drb__headerCompression__root__rohc__profiles__list__Format
    PDCP_Config__drb__headerCompression__root__rohc__profiles__F1 PDCP_Config__drb__headerCompression__root__rohc__profiles__F2 PDCP_Config__drb__headerCompression__root__rohc__profiles__F1F2_cond  PDCP_Config__drb__headerCompression__root__rohc__profiles__F1F2_cond2 PDCP_Config__drb__headerCompression__root__rohc__profiles__F2F1_cond.
Opaque PDCP_Config__drb__headerCompression__root__rohc__profiles__cond PDCP_Config__drb__headerCompression__root__rohc__profiles__Format.

Definition PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Format : T_Format PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__nat__Format PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F1 PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F2 PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F1F2 PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__F2F1.

Opaque PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__cond PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Format.


Definition PDCP_Config__drb__headerCompression__root__rohc__Format_Type := Eval cbn in seq_format_prod PDCP_Config__drb__headerCompression__root__rohc__list.
Definition PDCP_Config__drb__headerCompression__root__rohc__Format_list : PDCP_Config__drb__headerCompression__root__rohc__Format_Type :=
  (PDCP_Config__drb__headerCompression__root__rohc__maxCID__Format, (PDCP_Config__drb__headerCompression__root__rohc__profiles__Format, (PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC__Format, unit_format))).
Definition PDCP_Config__drb__headerCompression__root__rohc__list__Format := (*Eval compute in *) seq_format PDCP_Config__drb__headerCompression__root__rohc__list PDCP_Config__drb__headerCompression__root__rohc__Format_list.
Definition PDCP_Config__drb__headerCompression__root__rohc__F1 z :=
  (PDCP_Config__drb__headerCompression__root__rohc__maxCID z, (PDCP_Config__drb__headerCompression__root__rohc__profiles z, (PDCP_Config__drb__headerCompression__root__rohc__drb_ContinueROHC z, tt))).
Definition PDCP_Config__drb__headerCompression__root__rohc__F2 (y : seq_type PDCP_Config__drb__headerCompression__root__rohc__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PDCP_Config__drb__headerCompression__root__rohc__Type i0 i1 i2
  end.
Lemma PDCP_Config__drb__headerCompression__root__rohc__F1F2_cond (z : PDCP_Config__drb__headerCompression__root__rohc__Type)
  : PDCP_Config__drb__headerCompression__root__rohc__cond z ->
  (seq_cond PDCP_Config__drb__headerCompression__root__rohc__list (PDCP_Config__drb__headerCompression__root__rohc__F1 z)).
intro H. unfold PDCP_Config__drb__headerCompression__root__rohc__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__drb__headerCompression__root__rohc__F1F2_cond2 (z : PDCP_Config__drb__headerCompression__root__rohc__Type)
 : PDCP_Config__drb__headerCompression__root__rohc__F2 (PDCP_Config__drb__headerCompression__root__rohc__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__drb__headerCompression__root__rohc__F2F1_cond (y : seq_type PDCP_Config__drb__headerCompression__root__rohc__list)
  : seq_cond PDCP_Config__drb__headerCompression__root__rohc__list y ->
 (PDCP_Config__drb__headerCompression__root__rohc__cond (PDCP_Config__drb__headerCompression__root__rohc__F2 y)) /\  PDCP_Config__drb__headerCompression__root__rohc__F1 (PDCP_Config__drb__headerCompression__root__rohc__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__drb__headerCompression__root__rohc__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__drb__headerCompression__root__rohc__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__drb__headerCompression__root__rohc__Format : T_Format PDCP_Config__drb__headerCompression__root__rohc__Type PDCP_Config__drb__headerCompression__root__rohc__cond :=
        proj2_format  PDCP_Config__drb__headerCompression__root__rohc__cond PDCP_Config__drb__headerCompression__root__rohc__list__Format
    PDCP_Config__drb__headerCompression__root__rohc__F1 PDCP_Config__drb__headerCompression__root__rohc__F2 PDCP_Config__drb__headerCompression__root__rohc__F1F2_cond  PDCP_Config__drb__headerCompression__root__rohc__F1F2_cond2 PDCP_Config__drb__headerCompression__root__rohc__F2F1_cond.
Opaque PDCP_Config__drb__headerCompression__root__rohc__cond PDCP_Config__drb__headerCompression__root__rohc__Format.

Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__Format : T_Format Z PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond :=
 ranged_int_format (1) (16383) PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__helper1 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__helper2.

Opaque PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__Format.


Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Format_Type := Eval cbn in seq_format_prod PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Format_list : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Format_Type :=
  (bool__Format, unit_format).
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list__Format := (*Eval compute in *) seq_format PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Format_list.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1 z :=
  (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__profile0x0006 z, tt).
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F2 (y : seq_type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list) :=
  match y with
  | (i0, _)=>
    make__PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Type i0
  end.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1F2_cond (z : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Type)
  : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond z ->
  (seq_cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1 z)).
intro H. unfold PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1F2_cond2 (z : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Type)
 : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F2 (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F2F1_cond (y : seq_type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list)
  : seq_cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list y ->
 (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F2 y)) /\  PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1 (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Format : T_Format PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond :=
        proj2_format  PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__list__Format
    PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F2 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1F2_cond  PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F1F2_cond2 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__F2F1_cond.
Opaque PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Format.

Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Format : T_Format PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__nat__Format PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F1 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F2 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F1F2 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__F2F1.

Opaque PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Format.


Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Format_Type := Eval cbn in seq_format_prod PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Format_list : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Format_Type :=
  (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID__Format, (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles__Format, (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC__Format, unit_format))).
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list__Format := (*Eval compute in *) seq_format PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Format_list.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1 z :=
  (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__maxCID z, (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__profiles z, (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__drb_ContinueROHC z, tt))).
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F2 (y : seq_type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type i0 i1 i2
  end.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1F2_cond (z : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type)
  : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond z ->
  (seq_cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1 z)).
intro H. unfold PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1F2_cond2 (z : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type)
 : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F2 (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F2F1_cond (y : seq_type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list)
  : seq_cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list y ->
 (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F2 y)) /\  PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1 (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Format : T_Format PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond :=
        proj2_format  PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__list__Format
    PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F2 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1F2_cond  PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F1F2_cond2 PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__F2F1_cond.
Opaque PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__cond PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Format.


Definition PDCP_Config__drb__headerCompression__root__Format_Type := Eval cbn in get_formats PDCP_Config__drb__headerCompression__root__list.
Definition PDCP_Config__drb__headerCompression__root__Format_list : PDCP_Config__drb__headerCompression__root__Format_Type :=
  (unit__Format, (PDCP_Config__drb__headerCompression__root__rohc__Format, (PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Format, unit__Format))).
Definition PDCP_Config__drb__headerCompression__root__list__Format := Eval compute in choice_format PDCP_Config__drb__headerCompression__root__list PDCP_Config__drb__headerCompression__root__len_helper1 PDCP_Config__drb__headerCompression__root__len_helper2  PDCP_Config__drb__headerCompression__root__Format_list.
Definition PDCP_Config__drb__headerCompression__root__F1 (z : PDCP_Config__drb__headerCompression__root__Type) : (choice PDCP_Config__drb__headerCompression__root__list) :=
  match z with
   | PDCP_Config__drb__headerCompression__root__notUsed t => existT _ 0 t
  | PDCP_Config__drb__headerCompression__root__rohc t => existT _ 1 t
  | PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC t => existT _ 2 t
  end.
Definition PDCP_Config__drb__headerCompression__root__g := (fun n => typ_set (get_nth_typ PDCP_Config__drb__headerCompression__root__list n)).
Definition PDCP_Config__drb__headerCompression__root__F2 (y : choice PDCP_Config__drb__headerCompression__root__list) : PDCP_Config__drb__headerCompression__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDCP_Config__drb__headerCompression__root__g n -> PDCP_Config__drb__headerCompression__root__Type) with
    | 0 => fun (t : unit) => PDCP_Config__drb__headerCompression__root__notUsed t 
    | 1 => fun (t : PDCP_Config__drb__headerCompression__root__rohc__Type) => PDCP_Config__drb__headerCompression__root__rohc t 
    | 2 => fun (t : PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC__Type) => PDCP_Config__drb__headerCompression__root__uplinkOnlyROHC t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : PDCP_Config__drb__headerCompression__root__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ PDCP_Config__drb__headerCompression__root__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDCP_Config__drb__headerCompression__root__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return PDCP_Config__drb__headerCompression__root__Type with end) n0
           end t0).

Lemma PDCP_Config__drb__headerCompression__root__helper2 :  forall (y : PDCP_Config__drb__headerCompression__root__Type), PDCP_Config__drb__headerCompression__root__cond y -> choice_cond PDCP_Config__drb__headerCompression__root__list (PDCP_Config__drb__headerCompression__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDCP_Config__drb__headerCompression__root__helper3 :  forall (y : PDCP_Config__drb__headerCompression__root__Type), PDCP_Config__drb__headerCompression__root__F2 (PDCP_Config__drb__headerCompression__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDCP_Config__drb__headerCompression__root__helper4 : (forall b : choice PDCP_Config__drb__headerCompression__root__list, choice_cond PDCP_Config__drb__headerCompression__root__list b -> PDCP_Config__drb__headerCompression__root__cond (PDCP_Config__drb__headerCompression__root__F2 b) /\ PDCP_Config__drb__headerCompression__root__F1 (PDCP_Config__drb__headerCompression__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDCP_Config__drb__headerCompression__root__F1 PDCP_Config__drb__headerCompression__root__F2.
Definition PDCP_Config__drb__headerCompression__root__Format : T_Format PDCP_Config__drb__headerCompression__root__Type PDCP_Config__drb__headerCompression__root__cond :=
  (* Eval compute in *) proj2_format PDCP_Config__drb__headerCompression__root__cond PDCP_Config__drb__headerCompression__root__list__Format PDCP_Config__drb__headerCompression__root__F1 PDCP_Config__drb__headerCompression__root__F2 PDCP_Config__drb__headerCompression__root__helper2 PDCP_Config__drb__headerCompression__root__helper3 PDCP_Config__drb__headerCompression__root__helper4.
Opaque PDCP_Config__drb__headerCompression__root__cond PDCP_Config__drb__headerCompression__root__Format.

Definition PDCP_Config__drb__headerCompression__ext__Format : T_Format PDCP_Config__drb__headerCompression__ext__Type PDCP_Config__drb__headerCompression__ext__cond := empty_format.
Opaque PDCP_Config__drb__headerCompression__ext__cond PDCP_Config__drb__headerCompression__ext__Format.

Definition PDCP_Config__drb__headerCompression__Format : T_Format PDCP_Config__drb__headerCompression__Type PDCP_Config__drb__headerCompression__cond := sum_format PDCP_Config__drb__headerCompression__root__Format PDCP_Config__drb__headerCompression__ext__Format.
Opaque PDCP_Config__drb__headerCompression__cond PDCP_Config__drb__headerCompression__Format.

Definition PDCP_Config__drb__integrityProtection__Format : T_Format PDCP_Config__drb__integrityProtection__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__drb__integrityProtection__nat__Format PDCP_Config__drb__integrityProtection__F1 PDCP_Config__drb__integrityProtection__F2 PDCP_Config__drb__integrityProtection__F1F2 PDCP_Config__drb__integrityProtection__F2F1.

Opaque PDCP_Config__drb__integrityProtection__cond PDCP_Config__drb__integrityProtection__Format.

Definition PDCP_Config__drb__statusReportRequired__Format : T_Format PDCP_Config__drb__statusReportRequired__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__drb__statusReportRequired__nat__Format PDCP_Config__drb__statusReportRequired__F1 PDCP_Config__drb__statusReportRequired__F2 PDCP_Config__drb__statusReportRequired__F1F2 PDCP_Config__drb__statusReportRequired__F2F1.

Opaque PDCP_Config__drb__statusReportRequired__cond PDCP_Config__drb__statusReportRequired__Format.

Definition PDCP_Config__drb__outOfOrderDelivery__Format : T_Format PDCP_Config__drb__outOfOrderDelivery__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__drb__outOfOrderDelivery__nat__Format PDCP_Config__drb__outOfOrderDelivery__F1 PDCP_Config__drb__outOfOrderDelivery__F2 PDCP_Config__drb__outOfOrderDelivery__F1F2 PDCP_Config__drb__outOfOrderDelivery__F2F1.

Opaque PDCP_Config__drb__outOfOrderDelivery__cond PDCP_Config__drb__outOfOrderDelivery__Format.


Definition PDCP_Config__drb__Format_Type := Eval cbn in seq_format_prod PDCP_Config__drb__list.
Definition PDCP_Config__drb__Format_list : PDCP_Config__drb__Format_Type :=
  (PDCP_Config__drb__discardTimer__Format, (PDCP_Config__drb__pdcp_SN_SizeUL__Format, (PDCP_Config__drb__pdcp_SN_SizeDL__Format, (PDCP_Config__drb__headerCompression__Format, (PDCP_Config__drb__integrityProtection__Format, (PDCP_Config__drb__statusReportRequired__Format, (PDCP_Config__drb__outOfOrderDelivery__Format, unit_format))))))).
Definition PDCP_Config__drb__list__Format := (*Eval compute in *) seq_format PDCP_Config__drb__list PDCP_Config__drb__Format_list.
Definition PDCP_Config__drb__F1 z :=
  (PDCP_Config__drb__discardTimer z, (PDCP_Config__drb__pdcp_SN_SizeUL z, (PDCP_Config__drb__pdcp_SN_SizeDL z, (PDCP_Config__drb__headerCompression z, (PDCP_Config__drb__integrityProtection z, (PDCP_Config__drb__statusReportRequired z, (PDCP_Config__drb__outOfOrderDelivery z, tt))))))).
Definition PDCP_Config__drb__F2 (y : seq_type PDCP_Config__drb__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__PDCP_Config__drb__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma PDCP_Config__drb__F1F2_cond (z : PDCP_Config__drb__Type)
  : PDCP_Config__drb__cond z ->
  (seq_cond PDCP_Config__drb__list (PDCP_Config__drb__F1 z)).
intro H. unfold PDCP_Config__drb__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__drb__F1F2_cond2 (z : PDCP_Config__drb__Type)
 : PDCP_Config__drb__F2 (PDCP_Config__drb__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__drb__F2F1_cond (y : seq_type PDCP_Config__drb__list)
  : seq_cond PDCP_Config__drb__list y ->
 (PDCP_Config__drb__cond (PDCP_Config__drb__F2 y)) /\  PDCP_Config__drb__F1 (PDCP_Config__drb__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__drb__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__drb__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__drb__Format : T_Format PDCP_Config__drb__Type PDCP_Config__drb__cond :=
        proj2_format  PDCP_Config__drb__cond PDCP_Config__drb__list__Format
    PDCP_Config__drb__F1 PDCP_Config__drb__F2 PDCP_Config__drb__F1F2_cond  PDCP_Config__drb__F1F2_cond2 PDCP_Config__drb__F2F1_cond.
Opaque PDCP_Config__drb__cond PDCP_Config__drb__Format.


Definition PDCP_Config__moreThanOneRLC__primaryPath__Format_Type := Eval cbn in seq_format_prod PDCP_Config__moreThanOneRLC__primaryPath__list.
Definition PDCP_Config__moreThanOneRLC__primaryPath__Format_list : PDCP_Config__moreThanOneRLC__primaryPath__Format_Type :=
  (CellGroupId__Format, (LogicalChannelIdentity__Format, unit_format)).
Definition PDCP_Config__moreThanOneRLC__primaryPath__list__Format := (*Eval compute in *) seq_format PDCP_Config__moreThanOneRLC__primaryPath__list PDCP_Config__moreThanOneRLC__primaryPath__Format_list.
Definition PDCP_Config__moreThanOneRLC__primaryPath__F1 z :=
  (PDCP_Config__moreThanOneRLC__primaryPath__cellGroup z, (PDCP_Config__moreThanOneRLC__primaryPath__logicalChannel z, tt)).
Definition PDCP_Config__moreThanOneRLC__primaryPath__F2 (y : seq_type PDCP_Config__moreThanOneRLC__primaryPath__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDCP_Config__moreThanOneRLC__primaryPath__Type i0 i1
  end.
Lemma PDCP_Config__moreThanOneRLC__primaryPath__F1F2_cond (z : PDCP_Config__moreThanOneRLC__primaryPath__Type)
  : PDCP_Config__moreThanOneRLC__primaryPath__cond z ->
  (seq_cond PDCP_Config__moreThanOneRLC__primaryPath__list (PDCP_Config__moreThanOneRLC__primaryPath__F1 z)).
intro H. unfold PDCP_Config__moreThanOneRLC__primaryPath__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__moreThanOneRLC__primaryPath__F1F2_cond2 (z : PDCP_Config__moreThanOneRLC__primaryPath__Type)
 : PDCP_Config__moreThanOneRLC__primaryPath__F2 (PDCP_Config__moreThanOneRLC__primaryPath__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__moreThanOneRLC__primaryPath__F2F1_cond (y : seq_type PDCP_Config__moreThanOneRLC__primaryPath__list)
  : seq_cond PDCP_Config__moreThanOneRLC__primaryPath__list y ->
 (PDCP_Config__moreThanOneRLC__primaryPath__cond (PDCP_Config__moreThanOneRLC__primaryPath__F2 y)) /\  PDCP_Config__moreThanOneRLC__primaryPath__F1 (PDCP_Config__moreThanOneRLC__primaryPath__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__moreThanOneRLC__primaryPath__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__moreThanOneRLC__primaryPath__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__moreThanOneRLC__primaryPath__Format : T_Format PDCP_Config__moreThanOneRLC__primaryPath__Type PDCP_Config__moreThanOneRLC__primaryPath__cond :=
        proj2_format  PDCP_Config__moreThanOneRLC__primaryPath__cond PDCP_Config__moreThanOneRLC__primaryPath__list__Format
    PDCP_Config__moreThanOneRLC__primaryPath__F1 PDCP_Config__moreThanOneRLC__primaryPath__F2 PDCP_Config__moreThanOneRLC__primaryPath__F1F2_cond  PDCP_Config__moreThanOneRLC__primaryPath__F1F2_cond2 PDCP_Config__moreThanOneRLC__primaryPath__F2F1_cond.
Opaque PDCP_Config__moreThanOneRLC__primaryPath__cond PDCP_Config__moreThanOneRLC__primaryPath__Format.


Definition PDCP_Config__moreThanOneRLC__Format_Type := Eval cbn in seq_format_prod PDCP_Config__moreThanOneRLC__list.
Definition PDCP_Config__moreThanOneRLC__Format_list : PDCP_Config__moreThanOneRLC__Format_Type :=
  (PDCP_Config__moreThanOneRLC__primaryPath__Format, (UL_DataSplitThreshold__Format, (bool__Format, unit_format))).
Definition PDCP_Config__moreThanOneRLC__list__Format := (*Eval compute in *) seq_format PDCP_Config__moreThanOneRLC__list PDCP_Config__moreThanOneRLC__Format_list.
Definition PDCP_Config__moreThanOneRLC__F1 z :=
  (PDCP_Config__moreThanOneRLC__primaryPath z, (PDCP_Config__moreThanOneRLC__ul_DataSplitThreshold z, (PDCP_Config__moreThanOneRLC__pdcp_Duplication z, tt))).
Definition PDCP_Config__moreThanOneRLC__F2 (y : seq_type PDCP_Config__moreThanOneRLC__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PDCP_Config__moreThanOneRLC__Type i0 i1 i2
  end.
Lemma PDCP_Config__moreThanOneRLC__F1F2_cond (z : PDCP_Config__moreThanOneRLC__Type)
  : PDCP_Config__moreThanOneRLC__cond z ->
  (seq_cond PDCP_Config__moreThanOneRLC__list (PDCP_Config__moreThanOneRLC__F1 z)).
intro H. unfold PDCP_Config__moreThanOneRLC__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__moreThanOneRLC__F1F2_cond2 (z : PDCP_Config__moreThanOneRLC__Type)
 : PDCP_Config__moreThanOneRLC__F2 (PDCP_Config__moreThanOneRLC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__moreThanOneRLC__F2F1_cond (y : seq_type PDCP_Config__moreThanOneRLC__list)
  : seq_cond PDCP_Config__moreThanOneRLC__list y ->
 (PDCP_Config__moreThanOneRLC__cond (PDCP_Config__moreThanOneRLC__F2 y)) /\  PDCP_Config__moreThanOneRLC__F1 (PDCP_Config__moreThanOneRLC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__moreThanOneRLC__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__moreThanOneRLC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__moreThanOneRLC__Format : T_Format PDCP_Config__moreThanOneRLC__Type PDCP_Config__moreThanOneRLC__cond :=
        proj2_format  PDCP_Config__moreThanOneRLC__cond PDCP_Config__moreThanOneRLC__list__Format
    PDCP_Config__moreThanOneRLC__F1 PDCP_Config__moreThanOneRLC__F2 PDCP_Config__moreThanOneRLC__F1F2_cond  PDCP_Config__moreThanOneRLC__F1F2_cond2 PDCP_Config__moreThanOneRLC__F2F1_cond.
Opaque PDCP_Config__moreThanOneRLC__cond PDCP_Config__moreThanOneRLC__Format.

Definition PDCP_Config__t_Reordering__Format : T_Format PDCP_Config__t_Reordering__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__t_Reordering__nat__Format PDCP_Config__t_Reordering__F1 PDCP_Config__t_Reordering__F2 PDCP_Config__t_Reordering__F1F2 PDCP_Config__t_Reordering__F2F1.

Opaque PDCP_Config__t_Reordering__cond PDCP_Config__t_Reordering__Format.

Definition PDCP_Config__ext0O__cipheringDisabled__Format : T_Format PDCP_Config__ext0O__cipheringDisabled__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__ext0O__cipheringDisabled__nat__Format PDCP_Config__ext0O__cipheringDisabled__F1 PDCP_Config__ext0O__cipheringDisabled__F2 PDCP_Config__ext0O__cipheringDisabled__F1F2 PDCP_Config__ext0O__cipheringDisabled__F2F1.

Opaque PDCP_Config__ext0O__cipheringDisabled__cond PDCP_Config__ext0O__cipheringDisabled__Format.


Definition PDCP_Config__ext0O__Format_Type := Eval cbn in seq_format_prod PDCP_Config__ext0O__list.
Definition PDCP_Config__ext0O__Format_list : PDCP_Config__ext0O__Format_Type :=
  (PDCP_Config__ext0O__cipheringDisabled__Format, unit_format).
Definition PDCP_Config__ext0O__list__Format := (*Eval compute in *) seq_format PDCP_Config__ext0O__list PDCP_Config__ext0O__Format_list.
Definition PDCP_Config__ext0O__F1 z :=
  (PDCP_Config__ext0O__cipheringDisabled z, tt).
Definition PDCP_Config__ext0O__F2 (y : seq_type PDCP_Config__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PDCP_Config__ext0O__Type i0
  end.
Lemma PDCP_Config__ext0O__F1F2_cond (z : PDCP_Config__ext0O__Type)
  : PDCP_Config__ext0O__cond z ->
  (seq_cond PDCP_Config__ext0O__list (PDCP_Config__ext0O__F1 z)).
intro H. unfold PDCP_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__ext0O__F1F2_cond2 (z : PDCP_Config__ext0O__Type)
 : PDCP_Config__ext0O__F2 (PDCP_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__ext0O__F2F1_cond (y : seq_type PDCP_Config__ext0O__list)
  : seq_cond PDCP_Config__ext0O__list y ->
 (PDCP_Config__ext0O__cond (PDCP_Config__ext0O__F2 y)) /\  PDCP_Config__ext0O__F1 (PDCP_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__ext0O__Format : T_Format PDCP_Config__ext0O__Type PDCP_Config__ext0O__cond :=
        proj2_format  PDCP_Config__ext0O__cond PDCP_Config__ext0O__list__Format
    PDCP_Config__ext0O__F1 PDCP_Config__ext0O__F2 PDCP_Config__ext0O__F1F2_cond  PDCP_Config__ext0O__F1F2_cond2 PDCP_Config__ext0O__F2F1_cond.
Opaque PDCP_Config__ext0O__cond PDCP_Config__ext0O__Format.

Definition PDCP_Config__ext0__check_all_none (b : PDCP_Config__ext0O__Type) : bool :=
match b with 
  | make__PDCP_Config__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PDCP_Config__ext0__Format : T_Format PDCP_Config__ext0__Type PDCP_Config__ext0__cond :=
  restrict_add_format PDCP_Config__ext0__check_all_none PDCP_Config__ext0O__Format.

Opaque PDCP_Config__ext0__cond PDCP_Config__ext0__Format.

Opaque PDCP_Config__ext1O__discardTimerExt_r16__cond PDCP_Config__ext1O__discardTimerExt_r16__Format.

Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__Format : T_Format PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__Type PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__cond := seq_of_fixed_format bool__Format 3.

Opaque PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__cond PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__Format.


Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Format_Type := Eval cbn in seq_format_prod PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list.
Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Format_list : PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Format_Type :=
  (LogicalChannelIdentity__Format, (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16__Format, unit_format)).
Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list__Format := (*Eval compute in *) seq_format PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Format_list.
Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1 z :=
  (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__splitSecondaryPath_r16 z, (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__duplicationState_r16 z, tt)).
Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F2 (y : seq_type PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Type i0 i1
  end.
Lemma PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1F2_cond (z : PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Type)
  : PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond z ->
  (seq_cond PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1 z)).
intro H. unfold PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1F2_cond2 (z : PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Type)
 : PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F2 (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F2F1_cond (y : seq_type PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list)
  : seq_cond PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list y ->
 (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F2 y)) /\  PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1 (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Format : T_Format PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Type PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond :=
        proj2_format  PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__list__Format
    PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1 PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F2 PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1F2_cond  PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F1F2_cond2 PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__F2F1_cond.
Opaque PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__cond PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Format.

Opaque PDCP_Config__ext1O__ethernetHeaderCompression_r16__cond PDCP_Config__ext1O__ethernetHeaderCompression_r16__Format.


Definition PDCP_Config__ext1O__Format_Type := Eval cbn in seq_format_prod PDCP_Config__ext1O__list.
Definition PDCP_Config__ext1O__Format_list : PDCP_Config__ext1O__Format_Type :=
  (PDCP_Config__ext1O__discardTimerExt_r16__Format, (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16__Format, (PDCP_Config__ext1O__ethernetHeaderCompression_r16__Format, unit_format))).
Definition PDCP_Config__ext1O__list__Format := (*Eval compute in *) seq_format PDCP_Config__ext1O__list PDCP_Config__ext1O__Format_list.
Definition PDCP_Config__ext1O__F1 z :=
  (PDCP_Config__ext1O__discardTimerExt_r16 z, (PDCP_Config__ext1O__moreThanTwoRLC_DRB_r16 z, (PDCP_Config__ext1O__ethernetHeaderCompression_r16 z, tt))).
Definition PDCP_Config__ext1O__F2 (y : seq_type PDCP_Config__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PDCP_Config__ext1O__Type i0 i1 i2
  end.
Lemma PDCP_Config__ext1O__F1F2_cond (z : PDCP_Config__ext1O__Type)
  : PDCP_Config__ext1O__cond z ->
  (seq_cond PDCP_Config__ext1O__list (PDCP_Config__ext1O__F1 z)).
intro H. unfold PDCP_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__ext1O__F1F2_cond2 (z : PDCP_Config__ext1O__Type)
 : PDCP_Config__ext1O__F2 (PDCP_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__ext1O__F2F1_cond (y : seq_type PDCP_Config__ext1O__list)
  : seq_cond PDCP_Config__ext1O__list y ->
 (PDCP_Config__ext1O__cond (PDCP_Config__ext1O__F2 y)) /\  PDCP_Config__ext1O__F1 (PDCP_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__ext1O__Format : T_Format PDCP_Config__ext1O__Type PDCP_Config__ext1O__cond :=
        proj2_format  PDCP_Config__ext1O__cond PDCP_Config__ext1O__list__Format
    PDCP_Config__ext1O__F1 PDCP_Config__ext1O__F2 PDCP_Config__ext1O__F1F2_cond  PDCP_Config__ext1O__F1F2_cond2 PDCP_Config__ext1O__F2F1_cond.
Opaque PDCP_Config__ext1O__cond PDCP_Config__ext1O__Format.

Definition PDCP_Config__ext1__check_all_none (b : PDCP_Config__ext1O__Type) : bool :=
match b with 
  | make__PDCP_Config__ext1O__Type None None None  => false 
  | _ => true 
 end.
Definition PDCP_Config__ext1__Format : T_Format PDCP_Config__ext1__Type PDCP_Config__ext1__cond :=
  restrict_add_format PDCP_Config__ext1__check_all_none PDCP_Config__ext1O__Format.

Opaque PDCP_Config__ext1__cond PDCP_Config__ext1__Format.

Definition PDCP_Config__ext2O__survivalTimeStateSupport_r17__Format : T_Format PDCP_Config__ext2O__survivalTimeStateSupport_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCP_Config__ext2O__survivalTimeStateSupport_r17__nat__Format PDCP_Config__ext2O__survivalTimeStateSupport_r17__F1 PDCP_Config__ext2O__survivalTimeStateSupport_r17__F2 PDCP_Config__ext2O__survivalTimeStateSupport_r17__F1F2 PDCP_Config__ext2O__survivalTimeStateSupport_r17__F2F1.

Opaque PDCP_Config__ext2O__survivalTimeStateSupport_r17__cond PDCP_Config__ext2O__survivalTimeStateSupport_r17__Format.

Opaque PDCP_Config__ext2O__uplinkDataCompression_r17__cond PDCP_Config__ext2O__uplinkDataCompression_r17__Format.

Opaque PDCP_Config__ext2O__discardTimerExt2_r17__cond PDCP_Config__ext2O__discardTimerExt2_r17__Format.

Definition PDCP_Config__ext2O__initialRX_DELIV_r17__Format : T_Format PDCP_Config__ext2O__initialRX_DELIV_r17__Type PDCP_Config__ext2O__initialRX_DELIV_r17__cond := (* Eval compute in *) bit_string_fixed_format 32.
Opaque PDCP_Config__ext2O__initialRX_DELIV_r17__cond PDCP_Config__ext2O__initialRX_DELIV_r17__Format.


Definition PDCP_Config__ext2O__Format_Type := Eval cbn in seq_format_prod PDCP_Config__ext2O__list.
Definition PDCP_Config__ext2O__Format_list : PDCP_Config__ext2O__Format_Type :=
  (PDCP_Config__ext2O__survivalTimeStateSupport_r17__Format, (PDCP_Config__ext2O__uplinkDataCompression_r17__Format, (PDCP_Config__ext2O__discardTimerExt2_r17__Format, (PDCP_Config__ext2O__initialRX_DELIV_r17__Format, unit_format)))).
Definition PDCP_Config__ext2O__list__Format := (*Eval compute in *) seq_format PDCP_Config__ext2O__list PDCP_Config__ext2O__Format_list.
Definition PDCP_Config__ext2O__F1 z :=
  (PDCP_Config__ext2O__survivalTimeStateSupport_r17 z, (PDCP_Config__ext2O__uplinkDataCompression_r17 z, (PDCP_Config__ext2O__discardTimerExt2_r17 z, (PDCP_Config__ext2O__initialRX_DELIV_r17 z, tt)))).
Definition PDCP_Config__ext2O__F2 (y : seq_type PDCP_Config__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PDCP_Config__ext2O__Type i0 i1 i2 i3
  end.
Lemma PDCP_Config__ext2O__F1F2_cond (z : PDCP_Config__ext2O__Type)
  : PDCP_Config__ext2O__cond z ->
  (seq_cond PDCP_Config__ext2O__list (PDCP_Config__ext2O__F1 z)).
intro H. unfold PDCP_Config__ext2O__cond in H. simpl. auto. Qed.
Lemma PDCP_Config__ext2O__F1F2_cond2 (z : PDCP_Config__ext2O__Type)
 : PDCP_Config__ext2O__F2 (PDCP_Config__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCP_Config__ext2O__F2F1_cond (y : seq_type PDCP_Config__ext2O__list)
  : seq_cond PDCP_Config__ext2O__list y ->
 (PDCP_Config__ext2O__cond (PDCP_Config__ext2O__F2 y)) /\  PDCP_Config__ext2O__F1 (PDCP_Config__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCP_Config__ext2O__cond. simpl in *. auto.
 - simpl. unfold PDCP_Config__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCP_Config__ext2O__Format : T_Format PDCP_Config__ext2O__Type PDCP_Config__ext2O__cond :=
        proj2_format  PDCP_Config__ext2O__cond PDCP_Config__ext2O__list__Format
    PDCP_Config__ext2O__F1 PDCP_Config__ext2O__F2 PDCP_Config__ext2O__F1F2_cond  PDCP_Config__ext2O__F1F2_cond2 PDCP_Config__ext2O__F2F1_cond.
Opaque PDCP_Config__ext2O__cond PDCP_Config__ext2O__Format.

Definition PDCP_Config__ext2__check_all_none (b : PDCP_Config__ext2O__Type) : bool :=
match b with 
  | make__PDCP_Config__ext2O__Type None None None None  => false 
  | _ => true 
 end.
Definition PDCP_Config__ext2__Format : T_Format PDCP_Config__ext2__Type PDCP_Config__ext2__cond :=
  restrict_add_format PDCP_Config__ext2__check_all_none PDCP_Config__ext2O__Format.

Opaque PDCP_Config__ext2__cond PDCP_Config__ext2__Format.


Definition PDCP_Config__root_Format_Type := Eval cbn in seq_format_prod PDCP_Config__root_list.
Definition PDCP_Config__root_Format_list : PDCP_Config__root_Format_Type :=
  (PDCP_Config__drb__Format, (PDCP_Config__moreThanOneRLC__Format, (PDCP_Config__t_Reordering__Format, unit_format))).

Definition PDCP_Config__ext_Format_Type := Eval cbn in get_formats PDCP_Config__ext_list.
Definition PDCP_Config__ext_Format_list : PDCP_Config__ext_Format_Type :=
  (PDCP_Config__ext0__Format, (PDCP_Config__ext1__Format, (PDCP_Config__ext2__Format, unit__Format))).

Definition PDCP_Config__list_type : Set := (seq_type PDCP_Config__root_list) * (seq_ext_type PDCP_Config__ext_list).
Definition PDCP_Config__list_cond (z : PDCP_Config__list_type) : Prop :=
        (seq_cond PDCP_Config__root_list (fst z)) /\ (seq_ext_cond PDCP_Config__ext_list (snd z)).
Definition PDCP_Config__list_format : T_Format PDCP_Config__list_type PDCP_Config__list_cond :=
 (* Eval compute in *) seq_ext_format PDCP_Config__root_list PDCP_Config__root_Format_list PDCP_Config__ext_list PDCP_Config__ext_Format_list.

Opaque PDCP_Config__list_format.
Definition PDCP_Config__F1 (z : PDCP_Config__Type) : PDCP_Config__list_type :=
  (((PDCP_Config__drb z, (PDCP_Config__moreThanOneRLC z, (PDCP_Config__t_Reordering z, tt)))), (
(PDCP_Config__ext0 z, (PDCP_Config__ext1 z, (PDCP_Config__ext2 z, tt))))).
Definition PDCP_Config__F2 (y : PDCP_Config__list_type) : PDCP_Config__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, _))))=>
    make__PDCP_Config__Type j0 j1 j2 i0 i1 i2
  end.
Definition PDCP_Config__helper1 : (forall a : PDCP_Config__Type, PDCP_Config__cond a -> PDCP_Config__list_cond (PDCP_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDCP_Config__helper2 : (forall a : PDCP_Config__Type, PDCP_Config__F2 (PDCP_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDCP_Config__helper3 : (forall b : PDCP_Config__list_type, PDCP_Config__list_cond b -> PDCP_Config__cond (PDCP_Config__F2 b) /\ PDCP_Config__F1 (PDCP_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDCP_Config__cond, PDCP_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDCP_Config__Format : T_Format PDCP_Config__Type PDCP_Config__cond :=
 proj2_format PDCP_Config__cond PDCP_Config__list_format  PDCP_Config__F1 PDCP_Config__F2 PDCP_Config__helper1 PDCP_Config__helper2 PDCP_Config__helper3.

Opaque PDCP_Config__cond PDCP_Config__Format.

