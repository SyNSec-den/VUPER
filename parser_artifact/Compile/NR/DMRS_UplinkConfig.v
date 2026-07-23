Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DMRS_UplinkConfig__dmrs_Type__Type : Set :=
 | DMRS_UplinkConfig__dmrs_Type__type2
.
Definition DMRS_UplinkConfig__dmrs_Type__cond := (fun (_ : DMRS_UplinkConfig__dmrs_Type__Type) => True).
Lemma DMRS_UplinkConfig__dmrs_Type__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_UplinkConfig__dmrs_Type__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DMRS_UplinkConfig__dmrs_Type__nat__helper.

Definition DMRS_UplinkConfig__dmrs_Type__F1 t :=
  match t with
  | DMRS_UplinkConfig__dmrs_Type__type2 => 0
  end.
Definition DMRS_UplinkConfig__dmrs_Type__F2 n :=
  match n with
  | 0 => DMRS_UplinkConfig__dmrs_Type__type2
  | _ => DMRS_UplinkConfig__dmrs_Type__type2
  end.
Lemma DMRS_UplinkConfig__dmrs_Type__F1F2 : forall x : DMRS_UplinkConfig__dmrs_Type__Type, (DMRS_UplinkConfig__dmrs_Type__F1 x <= 0) /\ DMRS_UplinkConfig__dmrs_Type__F2 (DMRS_UplinkConfig__dmrs_Type__F1 x) = x. imp_solve. Qed.
Lemma DMRS_UplinkConfig__dmrs_Type__F2F1 : forall (y : nat) (H : y <= 0), DMRS_UplinkConfig__dmrs_Type__F1 (DMRS_UplinkConfig__dmrs_Type__F2 y) = y. enum_solve H y. Qed.

Inductive DMRS_UplinkConfig__dmrs_AdditionalPosition__Type : Set :=
 | DMRS_UplinkConfig__dmrs_AdditionalPosition__pos0
 | DMRS_UplinkConfig__dmrs_AdditionalPosition__pos1
 | DMRS_UplinkConfig__dmrs_AdditionalPosition__pos3
.
Definition DMRS_UplinkConfig__dmrs_AdditionalPosition__cond := (fun (_ : DMRS_UplinkConfig__dmrs_AdditionalPosition__Type) => True).
Lemma DMRS_UplinkConfig__dmrs_AdditionalPosition__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_UplinkConfig__dmrs_AdditionalPosition__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 DMRS_UplinkConfig__dmrs_AdditionalPosition__nat__helper.

Definition DMRS_UplinkConfig__dmrs_AdditionalPosition__F1 t :=
  match t with
  | DMRS_UplinkConfig__dmrs_AdditionalPosition__pos0 => 0
  | DMRS_UplinkConfig__dmrs_AdditionalPosition__pos1 => 1
  | DMRS_UplinkConfig__dmrs_AdditionalPosition__pos3 => 2
  end.
Definition DMRS_UplinkConfig__dmrs_AdditionalPosition__F2 n :=
  match n with
  | 0 => DMRS_UplinkConfig__dmrs_AdditionalPosition__pos0
  | 1 => DMRS_UplinkConfig__dmrs_AdditionalPosition__pos1
  | 2 => DMRS_UplinkConfig__dmrs_AdditionalPosition__pos3
  | _ => DMRS_UplinkConfig__dmrs_AdditionalPosition__pos0
  end.
Lemma DMRS_UplinkConfig__dmrs_AdditionalPosition__F1F2 : forall x : DMRS_UplinkConfig__dmrs_AdditionalPosition__Type, (DMRS_UplinkConfig__dmrs_AdditionalPosition__F1 x <= 2) /\ DMRS_UplinkConfig__dmrs_AdditionalPosition__F2 (DMRS_UplinkConfig__dmrs_AdditionalPosition__F1 x) = x. imp_solve. Qed.
Lemma DMRS_UplinkConfig__dmrs_AdditionalPosition__F2F1 : forall (y : nat) (H : y <= 2), DMRS_UplinkConfig__dmrs_AdditionalPosition__F1 (DMRS_UplinkConfig__dmrs_AdditionalPosition__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PTRS_UplinkConfig.
Definition DMRS_UplinkConfig__phaseTrackingRS__Type := SetupRelease__Type PTRS_UplinkConfig__Type.
Definition DMRS_UplinkConfig__phaseTrackingRS__cond := SetupRelease__cond _ PTRS_UplinkConfig__cond.
Definition DMRS_UplinkConfig__phaseTrackingRS__Format : T_Format DMRS_UplinkConfig__phaseTrackingRS__Type DMRS_UplinkConfig__phaseTrackingRS__cond := SetupRelease__Format _ _ PTRS_UplinkConfig__Format.
Opaque DMRS_UplinkConfig__phaseTrackingRS__cond DMRS_UplinkConfig__phaseTrackingRS__Format.

Inductive DMRS_UplinkConfig__maxLength__Type : Set :=
 | DMRS_UplinkConfig__maxLength__len2
.
Definition DMRS_UplinkConfig__maxLength__cond := (fun (_ : DMRS_UplinkConfig__maxLength__Type) => True).
Lemma DMRS_UplinkConfig__maxLength__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_UplinkConfig__maxLength__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DMRS_UplinkConfig__maxLength__nat__helper.

Definition DMRS_UplinkConfig__maxLength__F1 t :=
  match t with
  | DMRS_UplinkConfig__maxLength__len2 => 0
  end.
Definition DMRS_UplinkConfig__maxLength__F2 n :=
  match n with
  | 0 => DMRS_UplinkConfig__maxLength__len2
  | _ => DMRS_UplinkConfig__maxLength__len2
  end.
Lemma DMRS_UplinkConfig__maxLength__F1F2 : forall x : DMRS_UplinkConfig__maxLength__Type, (DMRS_UplinkConfig__maxLength__F1 x <= 0) /\ DMRS_UplinkConfig__maxLength__F2 (DMRS_UplinkConfig__maxLength__F1 x) = x. imp_solve. Qed.
Lemma DMRS_UplinkConfig__maxLength__F2F1 : forall (y : nat) (H : y <= 0), DMRS_UplinkConfig__maxLength__F1 (DMRS_UplinkConfig__maxLength__F2 y) = y. enum_solve H y. Qed.

Lemma DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__Type := Z.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__cond := (fun z => (0 <= z <= 65535)%Z).
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__Type := Z.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__cond := (fun z => (0 <= z <= 65535)%Z).
Inductive DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Type : Set :=
 | DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__enabled
.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__cond := (fun (_ : DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Type) => True).
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__nat__helper.

Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F1 t :=
  match t with
  | DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__enabled => 0
  end.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F2 n :=
  match n with
  | 0 => DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__enabled
  | _ => DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__enabled
  end.
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F1F2 : forall x : DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Type, (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F1 x <= 0) /\ DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F2 (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F1 x) = x. imp_solve. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F2F1 : forall (y : nat) (H : y <= 0), DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F1 (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F2 y) = y. enum_solve H y. Qed.

Record DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type : Set :=
  make__DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type {
    DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16 : option DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Type ;
}.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list := (
 Opt DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Type DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__cond ::
 nil).
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond z := 
  opt_cond DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__cond (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16 z) /\
  True.

Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0__Type := DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0__cond := DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond.

Record DMRS_UplinkConfig__transformPrecodingDisabled__Type : Set :=
  make__DMRS_UplinkConfig__transformPrecodingDisabled__Type {
    DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0 : option Z ;
    DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1 : option Z ;
    DMRS_UplinkConfig__transformPrecodingDisabled__ext0 : option DMRS_UplinkConfig__transformPrecodingDisabled__ext0__Type ;
}.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__root_list : list seq_elem := (
 Opt Z DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__cond ::
 Opt Z DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__cond ::
 nil).
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext_list : list typ := (
  typ_cons DMRS_UplinkConfig__transformPrecodingDisabled__ext0__Type DMRS_UplinkConfig__transformPrecodingDisabled__ext0__cond ::
  nil).
Definition DMRS_UplinkConfig__transformPrecodingDisabled__cond (z : DMRS_UplinkConfig__transformPrecodingDisabled__Type) := 
(  opt_cond DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__cond (DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0 z) /\
  opt_cond DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__cond (DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1 z) /\
  True) /\ 
(  opt_cond DMRS_UplinkConfig__transformPrecodingDisabled__ext0__cond (DMRS_UplinkConfig__transformPrecodingDisabled__ext0 z) /\
  True).

Lemma DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__helper1 : (0 <= 1007)%Z.  lia. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__helper2 : to_bit_sz (Z.to_nat (1007 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1007 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__Type := Z.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__cond := (fun z => (0 <= z <= 1007)%Z).
Inductive DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Type : Set :=
 | DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__disabled
.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__cond := (fun (_ : DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Type) => True).
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__nat__helper.

Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F1 t :=
  match t with
  | DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__disabled => 0
  end.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F2 n :=
  match n with
  | 0 => DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__disabled
  | _ => DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__disabled
  end.
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F1F2 : forall x : DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Type, (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F1 x <= 0) /\ DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F2 (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F1 x) = x. imp_solve. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F2F1 : forall (y : nat) (H : y <= 0), DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F1 (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F2 y) = y. enum_solve H y. Qed.

Inductive DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Type : Set :=
 | DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__enabled
.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__cond := (fun (_ : DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Type) => True).
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__nat__helper.

Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F1 t :=
  match t with
  | DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__enabled => 0
  end.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F2 n :=
  match n with
  | 0 => DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__enabled
  | _ => DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__enabled
  end.
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F1F2 : forall x : DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Type, (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F1 x <= 0) /\ DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F2 (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F1 x) = x. imp_solve. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F2F1 : forall (y : nat) (H : y <= 0), DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F1 (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.DMRS_UplinkTransformPrecoding_r16.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__Type := SetupRelease__Type DMRS_UplinkTransformPrecoding_r16__Type.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__cond := SetupRelease__cond _ DMRS_UplinkTransformPrecoding_r16__cond.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__Format : T_Format DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__Type DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__cond := SetupRelease__Format _ _ DMRS_UplinkTransformPrecoding_r16__Format.
Opaque DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__Format.

Record DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type : Set :=
  make__DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type {
    DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16 : option DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__Type ;
}.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list := (
 Opt DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__Type DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__cond ::
 nil).
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond z := 
  opt_cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__cond (DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16 z) /\
  True.

Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0__Type := DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0__cond := DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond.

Record DMRS_UplinkConfig__transformPrecodingEnabled__Type : Set :=
  make__DMRS_UplinkConfig__transformPrecodingEnabled__Type {
    DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity : option Z ;
    DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping : option DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Type ;
    DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping : option DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Type ;
    DMRS_UplinkConfig__transformPrecodingEnabled__ext0 : option DMRS_UplinkConfig__transformPrecodingEnabled__ext0__Type ;
}.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__root_list : list seq_elem := (
 Opt Z DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__cond ::
 Opt DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Type DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__cond ::
 Opt DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Type DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__cond ::
 nil).
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext_list : list typ := (
  typ_cons DMRS_UplinkConfig__transformPrecodingEnabled__ext0__Type DMRS_UplinkConfig__transformPrecodingEnabled__ext0__cond ::
  nil).
Definition DMRS_UplinkConfig__transformPrecodingEnabled__cond (z : DMRS_UplinkConfig__transformPrecodingEnabled__Type) := 
(  opt_cond DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__cond (DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity z) /\
  opt_cond DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__cond (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping z) /\
  opt_cond DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__cond (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping z) /\
  True) /\ 
(  opt_cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0__cond (DMRS_UplinkConfig__transformPrecodingEnabled__ext0 z) /\
  True).

Record DMRS_UplinkConfig__Type : Set :=
  make__DMRS_UplinkConfig__Type {
    DMRS_UplinkConfig__dmrs_Type : option DMRS_UplinkConfig__dmrs_Type__Type ;
    DMRS_UplinkConfig__dmrs_AdditionalPosition : option DMRS_UplinkConfig__dmrs_AdditionalPosition__Type ;
    DMRS_UplinkConfig__phaseTrackingRS : option DMRS_UplinkConfig__phaseTrackingRS__Type ;
    DMRS_UplinkConfig__maxLength : option DMRS_UplinkConfig__maxLength__Type ;
    DMRS_UplinkConfig__transformPrecodingDisabled : option DMRS_UplinkConfig__transformPrecodingDisabled__Type ;
    DMRS_UplinkConfig__transformPrecodingEnabled : option DMRS_UplinkConfig__transformPrecodingEnabled__Type ;
}.
Definition DMRS_UplinkConfig__root_list : list seq_elem := (
 Opt DMRS_UplinkConfig__dmrs_Type__Type DMRS_UplinkConfig__dmrs_Type__cond ::
 Opt DMRS_UplinkConfig__dmrs_AdditionalPosition__Type DMRS_UplinkConfig__dmrs_AdditionalPosition__cond ::
 Opt DMRS_UplinkConfig__phaseTrackingRS__Type DMRS_UplinkConfig__phaseTrackingRS__cond ::
 Opt DMRS_UplinkConfig__maxLength__Type DMRS_UplinkConfig__maxLength__cond ::
 Opt DMRS_UplinkConfig__transformPrecodingDisabled__Type DMRS_UplinkConfig__transformPrecodingDisabled__cond ::
 Opt DMRS_UplinkConfig__transformPrecodingEnabled__Type DMRS_UplinkConfig__transformPrecodingEnabled__cond ::
 nil).
Definition DMRS_UplinkConfig__ext_list : list typ := (
  nil).
Definition DMRS_UplinkConfig__cond (z : DMRS_UplinkConfig__Type) := 
(  opt_cond DMRS_UplinkConfig__dmrs_Type__cond (DMRS_UplinkConfig__dmrs_Type z) /\
  opt_cond DMRS_UplinkConfig__dmrs_AdditionalPosition__cond (DMRS_UplinkConfig__dmrs_AdditionalPosition z) /\
  opt_cond DMRS_UplinkConfig__phaseTrackingRS__cond (DMRS_UplinkConfig__phaseTrackingRS z) /\
  opt_cond DMRS_UplinkConfig__maxLength__cond (DMRS_UplinkConfig__maxLength z) /\
  opt_cond DMRS_UplinkConfig__transformPrecodingDisabled__cond (DMRS_UplinkConfig__transformPrecodingDisabled z) /\
  opt_cond DMRS_UplinkConfig__transformPrecodingEnabled__cond (DMRS_UplinkConfig__transformPrecodingEnabled z) /\
  True) /\ 
(  True).


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
Definition DMRS_UplinkConfig__dmrs_Type__Format : T_Format DMRS_UplinkConfig__dmrs_Type__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_UplinkConfig__dmrs_Type__nat__Format DMRS_UplinkConfig__dmrs_Type__F1 DMRS_UplinkConfig__dmrs_Type__F2 DMRS_UplinkConfig__dmrs_Type__F1F2 DMRS_UplinkConfig__dmrs_Type__F2F1.

Opaque DMRS_UplinkConfig__dmrs_Type__cond DMRS_UplinkConfig__dmrs_Type__Format.

Definition DMRS_UplinkConfig__dmrs_AdditionalPosition__Format : T_Format DMRS_UplinkConfig__dmrs_AdditionalPosition__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_UplinkConfig__dmrs_AdditionalPosition__nat__Format DMRS_UplinkConfig__dmrs_AdditionalPosition__F1 DMRS_UplinkConfig__dmrs_AdditionalPosition__F2 DMRS_UplinkConfig__dmrs_AdditionalPosition__F1F2 DMRS_UplinkConfig__dmrs_AdditionalPosition__F2F1.

Opaque DMRS_UplinkConfig__dmrs_AdditionalPosition__cond DMRS_UplinkConfig__dmrs_AdditionalPosition__Format.

Opaque DMRS_UplinkConfig__phaseTrackingRS__cond DMRS_UplinkConfig__phaseTrackingRS__Format.

Definition DMRS_UplinkConfig__maxLength__Format : T_Format DMRS_UplinkConfig__maxLength__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_UplinkConfig__maxLength__nat__Format DMRS_UplinkConfig__maxLength__F1 DMRS_UplinkConfig__maxLength__F2 DMRS_UplinkConfig__maxLength__F1F2 DMRS_UplinkConfig__maxLength__F2F1.

Opaque DMRS_UplinkConfig__maxLength__cond DMRS_UplinkConfig__maxLength__Format.

Definition DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__Format : T_Format Z DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__cond :=
 ranged_int_format (0) (65535) DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__helper1 DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__helper2.

Opaque DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__cond DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__Format.

Definition DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__Format : T_Format Z DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__cond :=
 ranged_int_format (0) (65535) DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__helper1 DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__helper2.

Opaque DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__cond DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__Format.

Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Format : T_Format DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__nat__Format DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F1 DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F2 DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F1F2 DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__F2F1.

Opaque DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__cond DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Format.


Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Format_Type := Eval cbn in seq_format_prod DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Format_list : DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Format_Type :=
  (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16__Format, unit_format).
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list__Format := (*Eval compute in *) seq_format DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Format_list.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1 z :=
  (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__dmrs_Uplink_r16 z, tt).
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F2 (y : seq_type DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type i0
  end.
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1F2_cond (z : DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type)
  : DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond z ->
  (seq_cond DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1 z)).
intro H. unfold DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond in H. simpl. auto. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1F2_cond2 (z : DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type)
 : DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F2 (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F2F1_cond (y : seq_type DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list)
  : seq_cond DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list y ->
 (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F2 y)) /\  DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1 (DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond. simpl in *. auto.
 - simpl. unfold DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Format : T_Format DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond :=
        proj2_format  DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__list__Format
    DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1 DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F2 DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1F2_cond  DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F1F2_cond2 DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__F2F1_cond.
Opaque DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__cond DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Format.

Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0__check_all_none (b : DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type) : bool :=
match b with 
  | make__DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Type None  => false 
  | _ => true 
 end.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext0__Format : T_Format DMRS_UplinkConfig__transformPrecodingDisabled__ext0__Type DMRS_UplinkConfig__transformPrecodingDisabled__ext0__cond :=
  restrict_add_format DMRS_UplinkConfig__transformPrecodingDisabled__ext0__check_all_none DMRS_UplinkConfig__transformPrecodingDisabled__ext0O__Format.

Opaque DMRS_UplinkConfig__transformPrecodingDisabled__ext0__cond DMRS_UplinkConfig__transformPrecodingDisabled__ext0__Format.


Definition DMRS_UplinkConfig__transformPrecodingDisabled__root_Format_Type := Eval cbn in seq_format_prod DMRS_UplinkConfig__transformPrecodingDisabled__root_list.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__root_Format_list : DMRS_UplinkConfig__transformPrecodingDisabled__root_Format_Type :=
  (DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0__Format, (DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1__Format, unit_format)).

Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext_Format_Type := Eval cbn in get_formats DMRS_UplinkConfig__transformPrecodingDisabled__ext_list.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__ext_Format_list : DMRS_UplinkConfig__transformPrecodingDisabled__ext_Format_Type :=
  (DMRS_UplinkConfig__transformPrecodingDisabled__ext0__Format, unit__Format).

Definition DMRS_UplinkConfig__transformPrecodingDisabled__list_type : Set := (seq_type DMRS_UplinkConfig__transformPrecodingDisabled__root_list) * (seq_ext_type DMRS_UplinkConfig__transformPrecodingDisabled__ext_list).
Definition DMRS_UplinkConfig__transformPrecodingDisabled__list_cond (z : DMRS_UplinkConfig__transformPrecodingDisabled__list_type) : Prop :=
        (seq_cond DMRS_UplinkConfig__transformPrecodingDisabled__root_list (fst z)) /\ (seq_ext_cond DMRS_UplinkConfig__transformPrecodingDisabled__ext_list (snd z)).
Definition DMRS_UplinkConfig__transformPrecodingDisabled__list_format : T_Format DMRS_UplinkConfig__transformPrecodingDisabled__list_type DMRS_UplinkConfig__transformPrecodingDisabled__list_cond :=
 (* Eval compute in *) seq_ext_format DMRS_UplinkConfig__transformPrecodingDisabled__root_list DMRS_UplinkConfig__transformPrecodingDisabled__root_Format_list DMRS_UplinkConfig__transformPrecodingDisabled__ext_list DMRS_UplinkConfig__transformPrecodingDisabled__ext_Format_list.

Opaque DMRS_UplinkConfig__transformPrecodingDisabled__list_format.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__F1 (z : DMRS_UplinkConfig__transformPrecodingDisabled__Type) : DMRS_UplinkConfig__transformPrecodingDisabled__list_type :=
  (((DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID0 z, (DMRS_UplinkConfig__transformPrecodingDisabled__scramblingID1 z, tt))), (
(DMRS_UplinkConfig__transformPrecodingDisabled__ext0 z, tt))).
Definition DMRS_UplinkConfig__transformPrecodingDisabled__F2 (y : DMRS_UplinkConfig__transformPrecodingDisabled__list_type) : DMRS_UplinkConfig__transformPrecodingDisabled__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__DMRS_UplinkConfig__transformPrecodingDisabled__Type j0 j1 i0
  end.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__helper1 : (forall a : DMRS_UplinkConfig__transformPrecodingDisabled__Type, DMRS_UplinkConfig__transformPrecodingDisabled__cond a -> DMRS_UplinkConfig__transformPrecodingDisabled__list_cond (DMRS_UplinkConfig__transformPrecodingDisabled__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__helper2 : (forall a : DMRS_UplinkConfig__transformPrecodingDisabled__Type, DMRS_UplinkConfig__transformPrecodingDisabled__F2 (DMRS_UplinkConfig__transformPrecodingDisabled__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__helper3 : (forall b : DMRS_UplinkConfig__transformPrecodingDisabled__list_type, DMRS_UplinkConfig__transformPrecodingDisabled__list_cond b -> DMRS_UplinkConfig__transformPrecodingDisabled__cond (DMRS_UplinkConfig__transformPrecodingDisabled__F2 b) /\ DMRS_UplinkConfig__transformPrecodingDisabled__F1 (DMRS_UplinkConfig__transformPrecodingDisabled__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DMRS_UplinkConfig__transformPrecodingDisabled__cond, DMRS_UplinkConfig__transformPrecodingDisabled__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DMRS_UplinkConfig__transformPrecodingDisabled__Format : T_Format DMRS_UplinkConfig__transformPrecodingDisabled__Type DMRS_UplinkConfig__transformPrecodingDisabled__cond :=
 proj2_format DMRS_UplinkConfig__transformPrecodingDisabled__cond DMRS_UplinkConfig__transformPrecodingDisabled__list_format  DMRS_UplinkConfig__transformPrecodingDisabled__F1 DMRS_UplinkConfig__transformPrecodingDisabled__F2 DMRS_UplinkConfig__transformPrecodingDisabled__helper1 DMRS_UplinkConfig__transformPrecodingDisabled__helper2 DMRS_UplinkConfig__transformPrecodingDisabled__helper3.

Opaque DMRS_UplinkConfig__transformPrecodingDisabled__cond DMRS_UplinkConfig__transformPrecodingDisabled__Format.

Definition DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__Format : T_Format Z DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__cond :=
 ranged_int_format (0) (1007) DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__helper1 DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__helper2.

Opaque DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__cond DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__Format.

Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Format : T_Format DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__nat__Format DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F1 DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F2 DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F1F2 DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__F2F1.

Opaque DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__cond DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Format.

Definition DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Format : T_Format DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__nat__Format DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F1 DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F2 DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F1F2 DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__F2F1.

Opaque DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__cond DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Format.

Opaque DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__Format.


Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Format_Type := Eval cbn in seq_format_prod DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Format_list : DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Format_Type :=
  (DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16__Format, unit_format).
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list__Format := (*Eval compute in *) seq_format DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Format_list.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1 z :=
  (DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__dmrs_UplinkTransformPrecoding_r16 z, tt).
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F2 (y : seq_type DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type i0
  end.
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1F2_cond (z : DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type)
  : DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond z ->
  (seq_cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list (DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1 z)).
intro H. unfold DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond in H. simpl. auto. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1F2_cond2 (z : DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type)
 : DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F2 (DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F2F1_cond (y : seq_type DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list)
  : seq_cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list y ->
 (DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond (DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F2 y)) /\  DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1 (DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond. simpl in *. auto.
 - simpl. unfold DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Format : T_Format DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond :=
        proj2_format  DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__list__Format
    DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1 DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F2 DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1F2_cond  DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F1F2_cond2 DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__F2F1_cond.
Opaque DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Format.

Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0__check_all_none (b : DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type) : bool :=
match b with 
  | make__DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Type None  => false 
  | _ => true 
 end.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext0__Format : T_Format DMRS_UplinkConfig__transformPrecodingEnabled__ext0__Type DMRS_UplinkConfig__transformPrecodingEnabled__ext0__cond :=
  restrict_add_format DMRS_UplinkConfig__transformPrecodingEnabled__ext0__check_all_none DMRS_UplinkConfig__transformPrecodingEnabled__ext0O__Format.

Opaque DMRS_UplinkConfig__transformPrecodingEnabled__ext0__cond DMRS_UplinkConfig__transformPrecodingEnabled__ext0__Format.


Definition DMRS_UplinkConfig__transformPrecodingEnabled__root_Format_Type := Eval cbn in seq_format_prod DMRS_UplinkConfig__transformPrecodingEnabled__root_list.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__root_Format_list : DMRS_UplinkConfig__transformPrecodingEnabled__root_Format_Type :=
  (DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity__Format, (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping__Format, (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping__Format, unit_format))).

Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext_Format_Type := Eval cbn in get_formats DMRS_UplinkConfig__transformPrecodingEnabled__ext_list.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__ext_Format_list : DMRS_UplinkConfig__transformPrecodingEnabled__ext_Format_Type :=
  (DMRS_UplinkConfig__transformPrecodingEnabled__ext0__Format, unit__Format).

Definition DMRS_UplinkConfig__transformPrecodingEnabled__list_type : Set := (seq_type DMRS_UplinkConfig__transformPrecodingEnabled__root_list) * (seq_ext_type DMRS_UplinkConfig__transformPrecodingEnabled__ext_list).
Definition DMRS_UplinkConfig__transformPrecodingEnabled__list_cond (z : DMRS_UplinkConfig__transformPrecodingEnabled__list_type) : Prop :=
        (seq_cond DMRS_UplinkConfig__transformPrecodingEnabled__root_list (fst z)) /\ (seq_ext_cond DMRS_UplinkConfig__transformPrecodingEnabled__ext_list (snd z)).
Definition DMRS_UplinkConfig__transformPrecodingEnabled__list_format : T_Format DMRS_UplinkConfig__transformPrecodingEnabled__list_type DMRS_UplinkConfig__transformPrecodingEnabled__list_cond :=
 (* Eval compute in *) seq_ext_format DMRS_UplinkConfig__transformPrecodingEnabled__root_list DMRS_UplinkConfig__transformPrecodingEnabled__root_Format_list DMRS_UplinkConfig__transformPrecodingEnabled__ext_list DMRS_UplinkConfig__transformPrecodingEnabled__ext_Format_list.

Opaque DMRS_UplinkConfig__transformPrecodingEnabled__list_format.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__F1 (z : DMRS_UplinkConfig__transformPrecodingEnabled__Type) : DMRS_UplinkConfig__transformPrecodingEnabled__list_type :=
  (((DMRS_UplinkConfig__transformPrecodingEnabled__nPUSCH_Identity z, (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceGroupHopping z, (DMRS_UplinkConfig__transformPrecodingEnabled__sequenceHopping z, tt)))), (
(DMRS_UplinkConfig__transformPrecodingEnabled__ext0 z, tt))).
Definition DMRS_UplinkConfig__transformPrecodingEnabled__F2 (y : DMRS_UplinkConfig__transformPrecodingEnabled__list_type) : DMRS_UplinkConfig__transformPrecodingEnabled__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__DMRS_UplinkConfig__transformPrecodingEnabled__Type j0 j1 j2 i0
  end.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__helper1 : (forall a : DMRS_UplinkConfig__transformPrecodingEnabled__Type, DMRS_UplinkConfig__transformPrecodingEnabled__cond a -> DMRS_UplinkConfig__transformPrecodingEnabled__list_cond (DMRS_UplinkConfig__transformPrecodingEnabled__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__helper2 : (forall a : DMRS_UplinkConfig__transformPrecodingEnabled__Type, DMRS_UplinkConfig__transformPrecodingEnabled__F2 (DMRS_UplinkConfig__transformPrecodingEnabled__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__helper3 : (forall b : DMRS_UplinkConfig__transformPrecodingEnabled__list_type, DMRS_UplinkConfig__transformPrecodingEnabled__list_cond b -> DMRS_UplinkConfig__transformPrecodingEnabled__cond (DMRS_UplinkConfig__transformPrecodingEnabled__F2 b) /\ DMRS_UplinkConfig__transformPrecodingEnabled__F1 (DMRS_UplinkConfig__transformPrecodingEnabled__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DMRS_UplinkConfig__transformPrecodingEnabled__cond, DMRS_UplinkConfig__transformPrecodingEnabled__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DMRS_UplinkConfig__transformPrecodingEnabled__Format : T_Format DMRS_UplinkConfig__transformPrecodingEnabled__Type DMRS_UplinkConfig__transformPrecodingEnabled__cond :=
 proj2_format DMRS_UplinkConfig__transformPrecodingEnabled__cond DMRS_UplinkConfig__transformPrecodingEnabled__list_format  DMRS_UplinkConfig__transformPrecodingEnabled__F1 DMRS_UplinkConfig__transformPrecodingEnabled__F2 DMRS_UplinkConfig__transformPrecodingEnabled__helper1 DMRS_UplinkConfig__transformPrecodingEnabled__helper2 DMRS_UplinkConfig__transformPrecodingEnabled__helper3.

Opaque DMRS_UplinkConfig__transformPrecodingEnabled__cond DMRS_UplinkConfig__transformPrecodingEnabled__Format.


Definition DMRS_UplinkConfig__root_Format_Type := Eval cbn in seq_format_prod DMRS_UplinkConfig__root_list.
Definition DMRS_UplinkConfig__root_Format_list : DMRS_UplinkConfig__root_Format_Type :=
  (DMRS_UplinkConfig__dmrs_Type__Format, (DMRS_UplinkConfig__dmrs_AdditionalPosition__Format, (DMRS_UplinkConfig__phaseTrackingRS__Format, (DMRS_UplinkConfig__maxLength__Format, (DMRS_UplinkConfig__transformPrecodingDisabled__Format, (DMRS_UplinkConfig__transformPrecodingEnabled__Format, unit_format)))))).

Definition DMRS_UplinkConfig__ext_Format_Type := Eval cbn in get_formats DMRS_UplinkConfig__ext_list.
Definition DMRS_UplinkConfig__ext_Format_list : DMRS_UplinkConfig__ext_Format_Type :=
  unit__Format.

Definition DMRS_UplinkConfig__list_type : Set := (seq_type DMRS_UplinkConfig__root_list) * (seq_ext_type DMRS_UplinkConfig__ext_list).
Definition DMRS_UplinkConfig__list_cond (z : DMRS_UplinkConfig__list_type) : Prop :=
        (seq_cond DMRS_UplinkConfig__root_list (fst z)) /\ (seq_ext_cond DMRS_UplinkConfig__ext_list (snd z)).
Definition DMRS_UplinkConfig__list_format : T_Format DMRS_UplinkConfig__list_type DMRS_UplinkConfig__list_cond :=
 (* Eval compute in *) seq_ext_format DMRS_UplinkConfig__root_list DMRS_UplinkConfig__root_Format_list DMRS_UplinkConfig__ext_list DMRS_UplinkConfig__ext_Format_list.

Opaque DMRS_UplinkConfig__list_format.
Definition DMRS_UplinkConfig__F1 (z : DMRS_UplinkConfig__Type) : DMRS_UplinkConfig__list_type :=
  (((DMRS_UplinkConfig__dmrs_Type z, (DMRS_UplinkConfig__dmrs_AdditionalPosition z, (DMRS_UplinkConfig__phaseTrackingRS z, (DMRS_UplinkConfig__maxLength z, (DMRS_UplinkConfig__transformPrecodingDisabled z, (DMRS_UplinkConfig__transformPrecodingEnabled z, tt))))))), (
tt)).
Definition DMRS_UplinkConfig__F2 (y : DMRS_UplinkConfig__list_type) : DMRS_UplinkConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__DMRS_UplinkConfig__Type j0 j1 j2 j3 j4 j5
  end.
Definition DMRS_UplinkConfig__helper1 : (forall a : DMRS_UplinkConfig__Type, DMRS_UplinkConfig__cond a -> DMRS_UplinkConfig__list_cond (DMRS_UplinkConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DMRS_UplinkConfig__helper2 : (forall a : DMRS_UplinkConfig__Type, DMRS_UplinkConfig__F2 (DMRS_UplinkConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DMRS_UplinkConfig__helper3 : (forall b : DMRS_UplinkConfig__list_type, DMRS_UplinkConfig__list_cond b -> DMRS_UplinkConfig__cond (DMRS_UplinkConfig__F2 b) /\ DMRS_UplinkConfig__F1 (DMRS_UplinkConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DMRS_UplinkConfig__cond, DMRS_UplinkConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DMRS_UplinkConfig__Format : T_Format DMRS_UplinkConfig__Type DMRS_UplinkConfig__cond :=
 proj2_format DMRS_UplinkConfig__cond DMRS_UplinkConfig__list_format  DMRS_UplinkConfig__F1 DMRS_UplinkConfig__F2 DMRS_UplinkConfig__helper1 DMRS_UplinkConfig__helper2 DMRS_UplinkConfig__helper3.

Opaque DMRS_UplinkConfig__cond DMRS_UplinkConfig__Format.

