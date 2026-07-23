Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.PDSCH_CodeBlockGroupTransmission.
Definition PDSCH_ServingCellConfig__codeBlockGroupTransmission__Type := SetupRelease__Type PDSCH_CodeBlockGroupTransmission__Type.
Definition PDSCH_ServingCellConfig__codeBlockGroupTransmission__cond := SetupRelease__cond _ PDSCH_CodeBlockGroupTransmission__cond.
Definition PDSCH_ServingCellConfig__codeBlockGroupTransmission__Format : T_Format PDSCH_ServingCellConfig__codeBlockGroupTransmission__Type PDSCH_ServingCellConfig__codeBlockGroupTransmission__cond := SetupRelease__Format _ _ PDSCH_CodeBlockGroupTransmission__Format.
Opaque PDSCH_ServingCellConfig__codeBlockGroupTransmission__cond PDSCH_ServingCellConfig__codeBlockGroupTransmission__Format.

Inductive PDSCH_ServingCellConfig__xOverhead__Type : Set :=
 | PDSCH_ServingCellConfig__xOverhead__xOh6
 | PDSCH_ServingCellConfig__xOverhead__xOh12
 | PDSCH_ServingCellConfig__xOverhead__xOh18
.
Definition PDSCH_ServingCellConfig__xOverhead__cond := (fun (_ : PDSCH_ServingCellConfig__xOverhead__Type) => True).
Lemma PDSCH_ServingCellConfig__xOverhead__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_ServingCellConfig__xOverhead__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PDSCH_ServingCellConfig__xOverhead__nat__helper.

Definition PDSCH_ServingCellConfig__xOverhead__F1 t :=
  match t with
  | PDSCH_ServingCellConfig__xOverhead__xOh6 => 0
  | PDSCH_ServingCellConfig__xOverhead__xOh12 => 1
  | PDSCH_ServingCellConfig__xOverhead__xOh18 => 2
  end.
Definition PDSCH_ServingCellConfig__xOverhead__F2 n :=
  match n with
  | 0 => PDSCH_ServingCellConfig__xOverhead__xOh6
  | 1 => PDSCH_ServingCellConfig__xOverhead__xOh12
  | 2 => PDSCH_ServingCellConfig__xOverhead__xOh18
  | _ => PDSCH_ServingCellConfig__xOverhead__xOh6
  end.
Lemma PDSCH_ServingCellConfig__xOverhead__F1F2 : forall x : PDSCH_ServingCellConfig__xOverhead__Type, (PDSCH_ServingCellConfig__xOverhead__F1 x <= 2) /\ PDSCH_ServingCellConfig__xOverhead__F2 (PDSCH_ServingCellConfig__xOverhead__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_ServingCellConfig__xOverhead__F2F1 : forall (y : nat) (H : y <= 2), PDSCH_ServingCellConfig__xOverhead__F1 (PDSCH_ServingCellConfig__xOverhead__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Type : Set :=
 | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n2
 | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n4
 | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n6
 | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n10
 | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n12
 | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n16
.
Definition PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__cond := (fun (_ : PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Type) => True).
Lemma PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__nat__helper.

Definition PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F1 t :=
  match t with
  | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n2 => 0
  | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n4 => 1
  | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n6 => 2
  | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n10 => 3
  | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n12 => 4
  | PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n16 => 5
  end.
Definition PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F2 n :=
  match n with
  | 0 => PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n2
  | 1 => PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n4
  | 2 => PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n6
  | 3 => PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n10
  | 4 => PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n12
  | 5 => PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n16
  | _ => PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__n2
  end.
Lemma PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F1F2 : forall x : PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Type, (PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F1 x <= 5) /\ PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F2 (PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F2F1 : forall (y : nat) (H : y <= 5), PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F1 (PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Lemma PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__Type := Z.
Definition PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond := (fun z => (1 <= z <= 8)%Z).
Record PDSCH_ServingCellConfig__ext0O__Type : Set :=
  make__PDSCH_ServingCellConfig__ext0O__Type {
    PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers : option Z ;
    PDSCH_ServingCellConfig__ext0O__processingType2Enabled : option bool ;
}.
Definition PDSCH_ServingCellConfig__ext0O__list := (
 Opt Z PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond ::
 Opt bool (fun _ => True) ::
 nil).
Definition PDSCH_ServingCellConfig__ext0O__cond z := 
  opt_cond PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond (PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers z) /\
  opt_cond (fun _ => True) (PDSCH_ServingCellConfig__ext0O__processingType2Enabled z) /\
  True.

Definition PDSCH_ServingCellConfig__ext0__Type := PDSCH_ServingCellConfig__ext0O__Type.
Definition PDSCH_ServingCellConfig__ext0__cond := PDSCH_ServingCellConfig__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.PDSCH_CodeBlockGroupTransmissionList_r16.
Definition PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__Type := SetupRelease__Type PDSCH_CodeBlockGroupTransmissionList_r16__Type.
Definition PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__cond := SetupRelease__cond _ PDSCH_CodeBlockGroupTransmissionList_r16__cond.
Definition PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__Format : T_Format PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__Type PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__cond := SetupRelease__Format _ _ PDSCH_CodeBlockGroupTransmissionList_r16__Format.
Opaque PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__cond PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__Format.

Record PDSCH_ServingCellConfig__ext1O__Type : Set :=
  make__PDSCH_ServingCellConfig__ext1O__Type {
    PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16 : option PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__Type ;
}.
Definition PDSCH_ServingCellConfig__ext1O__list := (
 Opt PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__Type PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__cond ::
 nil).
Definition PDSCH_ServingCellConfig__ext1O__cond z := 
  opt_cond PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__cond (PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16 z) /\
  True.

Definition PDSCH_ServingCellConfig__ext1__Type := PDSCH_ServingCellConfig__ext1O__Type.
Definition PDSCH_ServingCellConfig__ext1__cond := PDSCH_ServingCellConfig__ext1O__cond.

Require Import NR.SetupRelease.
Require Import NR.DownlinkHARQ_FeedbackDisabled_r17.
Definition PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__Type := SetupRelease__Type DownlinkHARQ_FeedbackDisabled_r17__Type.
Definition PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__cond := SetupRelease__cond _ DownlinkHARQ_FeedbackDisabled_r17__cond.
Definition PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__Format : T_Format PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__Type PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__cond := SetupRelease__Format _ _ DownlinkHARQ_FeedbackDisabled_r17__Format.
Opaque PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__cond PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__Format.

Inductive PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Type : Set :=
 | PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__n32
.
Definition PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__cond := (fun (_ : PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Type) => True).
Lemma PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__nat__helper.

Definition PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F1 t :=
  match t with
  | PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__n32 => 0
  end.
Definition PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F2 n :=
  match n with
  | 0 => PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__n32
  | _ => PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__n32
  end.
Lemma PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F1F2 : forall x : PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Type, (PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F1 x <= 0) /\ PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F2 (PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F1 (PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_ServingCellConfig__ext2O__Type : Set :=
  make__PDSCH_ServingCellConfig__ext2O__Type {
    PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17 : option PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__Type ;
    PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700 : option PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Type ;
}.
Definition PDSCH_ServingCellConfig__ext2O__list := (
 Opt PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__Type PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__cond ::
 Opt PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Type PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__cond ::
 nil).
Definition PDSCH_ServingCellConfig__ext2O__cond z := 
  opt_cond PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__cond (PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17 z) /\
  opt_cond PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__cond (PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700 z) /\
  True.

Definition PDSCH_ServingCellConfig__ext2__Type := PDSCH_ServingCellConfig__ext2O__Type.
Definition PDSCH_ServingCellConfig__ext2__cond := PDSCH_ServingCellConfig__ext2O__cond.

Record PDSCH_ServingCellConfig__Type : Set :=
  make__PDSCH_ServingCellConfig__Type {
    PDSCH_ServingCellConfig__codeBlockGroupTransmission : option PDSCH_ServingCellConfig__codeBlockGroupTransmission__Type ;
    PDSCH_ServingCellConfig__xOverhead : option PDSCH_ServingCellConfig__xOverhead__Type ;
    PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH : option PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Type ;
    PDSCH_ServingCellConfig__pucch_Cell : option ServCellIndex__Type ;
    PDSCH_ServingCellConfig__ext0 : option PDSCH_ServingCellConfig__ext0__Type ;
    PDSCH_ServingCellConfig__ext1 : option PDSCH_ServingCellConfig__ext1__Type ;
    PDSCH_ServingCellConfig__ext2 : option PDSCH_ServingCellConfig__ext2__Type ;
}.
Definition PDSCH_ServingCellConfig__root_list : list seq_elem := (
 Opt PDSCH_ServingCellConfig__codeBlockGroupTransmission__Type PDSCH_ServingCellConfig__codeBlockGroupTransmission__cond ::
 Opt PDSCH_ServingCellConfig__xOverhead__Type PDSCH_ServingCellConfig__xOverhead__cond ::
 Opt PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Type PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 nil).
Definition PDSCH_ServingCellConfig__ext_list : list typ := (
  typ_cons PDSCH_ServingCellConfig__ext0__Type PDSCH_ServingCellConfig__ext0__cond ::
  typ_cons PDSCH_ServingCellConfig__ext1__Type PDSCH_ServingCellConfig__ext1__cond ::
  typ_cons PDSCH_ServingCellConfig__ext2__Type PDSCH_ServingCellConfig__ext2__cond ::
  nil).
Definition PDSCH_ServingCellConfig__cond (z : PDSCH_ServingCellConfig__Type) := 
(  opt_cond PDSCH_ServingCellConfig__codeBlockGroupTransmission__cond (PDSCH_ServingCellConfig__codeBlockGroupTransmission z) /\
  opt_cond PDSCH_ServingCellConfig__xOverhead__cond (PDSCH_ServingCellConfig__xOverhead z) /\
  opt_cond PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__cond (PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH z) /\
  opt_cond ServCellIndex__cond (PDSCH_ServingCellConfig__pucch_Cell z) /\
  True) /\ 
(  opt_cond PDSCH_ServingCellConfig__ext0__cond (PDSCH_ServingCellConfig__ext0 z) /\
  opt_cond PDSCH_ServingCellConfig__ext1__cond (PDSCH_ServingCellConfig__ext1 z) /\
  opt_cond PDSCH_ServingCellConfig__ext2__cond (PDSCH_ServingCellConfig__ext2 z) /\
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
Opaque PDSCH_ServingCellConfig__codeBlockGroupTransmission__cond PDSCH_ServingCellConfig__codeBlockGroupTransmission__Format.

Definition PDSCH_ServingCellConfig__xOverhead__Format : T_Format PDSCH_ServingCellConfig__xOverhead__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_ServingCellConfig__xOverhead__nat__Format PDSCH_ServingCellConfig__xOverhead__F1 PDSCH_ServingCellConfig__xOverhead__F2 PDSCH_ServingCellConfig__xOverhead__F1F2 PDSCH_ServingCellConfig__xOverhead__F2F1.

Opaque PDSCH_ServingCellConfig__xOverhead__cond PDSCH_ServingCellConfig__xOverhead__Format.

Definition PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Format : T_Format PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__nat__Format PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F1 PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F2 PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F1F2 PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__F2F1.

Opaque PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__cond PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Format.

Definition PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__Format : T_Format Z PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond :=
 ranged_int_format (1) (8) PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper1 PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper2.

Opaque PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__Format.


Definition PDSCH_ServingCellConfig__ext0O__Format_Type := Eval cbn in seq_format_prod PDSCH_ServingCellConfig__ext0O__list.
Definition PDSCH_ServingCellConfig__ext0O__Format_list : PDSCH_ServingCellConfig__ext0O__Format_Type :=
  (PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers__Format, (bool__Format, unit_format)).
Definition PDSCH_ServingCellConfig__ext0O__list__Format := (*Eval compute in *) seq_format PDSCH_ServingCellConfig__ext0O__list PDSCH_ServingCellConfig__ext0O__Format_list.
Definition PDSCH_ServingCellConfig__ext0O__F1 z :=
  (PDSCH_ServingCellConfig__ext0O__maxMIMO_Layers z, (PDSCH_ServingCellConfig__ext0O__processingType2Enabled z, tt)).
Definition PDSCH_ServingCellConfig__ext0O__F2 (y : seq_type PDSCH_ServingCellConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDSCH_ServingCellConfig__ext0O__Type i0 i1
  end.
Lemma PDSCH_ServingCellConfig__ext0O__F1F2_cond (z : PDSCH_ServingCellConfig__ext0O__Type)
  : PDSCH_ServingCellConfig__ext0O__cond z ->
  (seq_cond PDSCH_ServingCellConfig__ext0O__list (PDSCH_ServingCellConfig__ext0O__F1 z)).
intro H. unfold PDSCH_ServingCellConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma PDSCH_ServingCellConfig__ext0O__F1F2_cond2 (z : PDSCH_ServingCellConfig__ext0O__Type)
 : PDSCH_ServingCellConfig__ext0O__F2 (PDSCH_ServingCellConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_ServingCellConfig__ext0O__F2F1_cond (y : seq_type PDSCH_ServingCellConfig__ext0O__list)
  : seq_cond PDSCH_ServingCellConfig__ext0O__list y ->
 (PDSCH_ServingCellConfig__ext0O__cond (PDSCH_ServingCellConfig__ext0O__F2 y)) /\  PDSCH_ServingCellConfig__ext0O__F1 (PDSCH_ServingCellConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_ServingCellConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_ServingCellConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_ServingCellConfig__ext0O__Format : T_Format PDSCH_ServingCellConfig__ext0O__Type PDSCH_ServingCellConfig__ext0O__cond :=
        proj2_format  PDSCH_ServingCellConfig__ext0O__cond PDSCH_ServingCellConfig__ext0O__list__Format
    PDSCH_ServingCellConfig__ext0O__F1 PDSCH_ServingCellConfig__ext0O__F2 PDSCH_ServingCellConfig__ext0O__F1F2_cond  PDSCH_ServingCellConfig__ext0O__F1F2_cond2 PDSCH_ServingCellConfig__ext0O__F2F1_cond.
Opaque PDSCH_ServingCellConfig__ext0O__cond PDSCH_ServingCellConfig__ext0O__Format.

Definition PDSCH_ServingCellConfig__ext0__check_all_none (b : PDSCH_ServingCellConfig__ext0O__Type) : bool :=
match b with 
  | make__PDSCH_ServingCellConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition PDSCH_ServingCellConfig__ext0__Format : T_Format PDSCH_ServingCellConfig__ext0__Type PDSCH_ServingCellConfig__ext0__cond :=
  restrict_add_format PDSCH_ServingCellConfig__ext0__check_all_none PDSCH_ServingCellConfig__ext0O__Format.

Opaque PDSCH_ServingCellConfig__ext0__cond PDSCH_ServingCellConfig__ext0__Format.

Opaque PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__cond PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__Format.


Definition PDSCH_ServingCellConfig__ext1O__Format_Type := Eval cbn in seq_format_prod PDSCH_ServingCellConfig__ext1O__list.
Definition PDSCH_ServingCellConfig__ext1O__Format_list : PDSCH_ServingCellConfig__ext1O__Format_Type :=
  (PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16__Format, unit_format).
Definition PDSCH_ServingCellConfig__ext1O__list__Format := (*Eval compute in *) seq_format PDSCH_ServingCellConfig__ext1O__list PDSCH_ServingCellConfig__ext1O__Format_list.
Definition PDSCH_ServingCellConfig__ext1O__F1 z :=
  (PDSCH_ServingCellConfig__ext1O__pdsch_CodeBlockGroupTransmissionList_r16 z, tt).
Definition PDSCH_ServingCellConfig__ext1O__F2 (y : seq_type PDSCH_ServingCellConfig__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__PDSCH_ServingCellConfig__ext1O__Type i0
  end.
Lemma PDSCH_ServingCellConfig__ext1O__F1F2_cond (z : PDSCH_ServingCellConfig__ext1O__Type)
  : PDSCH_ServingCellConfig__ext1O__cond z ->
  (seq_cond PDSCH_ServingCellConfig__ext1O__list (PDSCH_ServingCellConfig__ext1O__F1 z)).
intro H. unfold PDSCH_ServingCellConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma PDSCH_ServingCellConfig__ext1O__F1F2_cond2 (z : PDSCH_ServingCellConfig__ext1O__Type)
 : PDSCH_ServingCellConfig__ext1O__F2 (PDSCH_ServingCellConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_ServingCellConfig__ext1O__F2F1_cond (y : seq_type PDSCH_ServingCellConfig__ext1O__list)
  : seq_cond PDSCH_ServingCellConfig__ext1O__list y ->
 (PDSCH_ServingCellConfig__ext1O__cond (PDSCH_ServingCellConfig__ext1O__F2 y)) /\  PDSCH_ServingCellConfig__ext1O__F1 (PDSCH_ServingCellConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_ServingCellConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_ServingCellConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_ServingCellConfig__ext1O__Format : T_Format PDSCH_ServingCellConfig__ext1O__Type PDSCH_ServingCellConfig__ext1O__cond :=
        proj2_format  PDSCH_ServingCellConfig__ext1O__cond PDSCH_ServingCellConfig__ext1O__list__Format
    PDSCH_ServingCellConfig__ext1O__F1 PDSCH_ServingCellConfig__ext1O__F2 PDSCH_ServingCellConfig__ext1O__F1F2_cond  PDSCH_ServingCellConfig__ext1O__F1F2_cond2 PDSCH_ServingCellConfig__ext1O__F2F1_cond.
Opaque PDSCH_ServingCellConfig__ext1O__cond PDSCH_ServingCellConfig__ext1O__Format.

Definition PDSCH_ServingCellConfig__ext1__check_all_none (b : PDSCH_ServingCellConfig__ext1O__Type) : bool :=
match b with 
  | make__PDSCH_ServingCellConfig__ext1O__Type None  => false 
  | _ => true 
 end.
Definition PDSCH_ServingCellConfig__ext1__Format : T_Format PDSCH_ServingCellConfig__ext1__Type PDSCH_ServingCellConfig__ext1__cond :=
  restrict_add_format PDSCH_ServingCellConfig__ext1__check_all_none PDSCH_ServingCellConfig__ext1O__Format.

Opaque PDSCH_ServingCellConfig__ext1__cond PDSCH_ServingCellConfig__ext1__Format.

Opaque PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__cond PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__Format.

Definition PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Format : T_Format PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__nat__Format PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F1 PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F2 PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F1F2 PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__F2F1.

Opaque PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__cond PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Format.


Definition PDSCH_ServingCellConfig__ext2O__Format_Type := Eval cbn in seq_format_prod PDSCH_ServingCellConfig__ext2O__list.
Definition PDSCH_ServingCellConfig__ext2O__Format_list : PDSCH_ServingCellConfig__ext2O__Format_Type :=
  (PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17__Format, (PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700__Format, unit_format)).
Definition PDSCH_ServingCellConfig__ext2O__list__Format := (*Eval compute in *) seq_format PDSCH_ServingCellConfig__ext2O__list PDSCH_ServingCellConfig__ext2O__Format_list.
Definition PDSCH_ServingCellConfig__ext2O__F1 z :=
  (PDSCH_ServingCellConfig__ext2O__downlinkHARQ_FeedbackDisabled_r17 z, (PDSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPDSCH_v1700 z, tt)).
Definition PDSCH_ServingCellConfig__ext2O__F2 (y : seq_type PDSCH_ServingCellConfig__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDSCH_ServingCellConfig__ext2O__Type i0 i1
  end.
Lemma PDSCH_ServingCellConfig__ext2O__F1F2_cond (z : PDSCH_ServingCellConfig__ext2O__Type)
  : PDSCH_ServingCellConfig__ext2O__cond z ->
  (seq_cond PDSCH_ServingCellConfig__ext2O__list (PDSCH_ServingCellConfig__ext2O__F1 z)).
intro H. unfold PDSCH_ServingCellConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma PDSCH_ServingCellConfig__ext2O__F1F2_cond2 (z : PDSCH_ServingCellConfig__ext2O__Type)
 : PDSCH_ServingCellConfig__ext2O__F2 (PDSCH_ServingCellConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_ServingCellConfig__ext2O__F2F1_cond (y : seq_type PDSCH_ServingCellConfig__ext2O__list)
  : seq_cond PDSCH_ServingCellConfig__ext2O__list y ->
 (PDSCH_ServingCellConfig__ext2O__cond (PDSCH_ServingCellConfig__ext2O__F2 y)) /\  PDSCH_ServingCellConfig__ext2O__F1 (PDSCH_ServingCellConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_ServingCellConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_ServingCellConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_ServingCellConfig__ext2O__Format : T_Format PDSCH_ServingCellConfig__ext2O__Type PDSCH_ServingCellConfig__ext2O__cond :=
        proj2_format  PDSCH_ServingCellConfig__ext2O__cond PDSCH_ServingCellConfig__ext2O__list__Format
    PDSCH_ServingCellConfig__ext2O__F1 PDSCH_ServingCellConfig__ext2O__F2 PDSCH_ServingCellConfig__ext2O__F1F2_cond  PDSCH_ServingCellConfig__ext2O__F1F2_cond2 PDSCH_ServingCellConfig__ext2O__F2F1_cond.
Opaque PDSCH_ServingCellConfig__ext2O__cond PDSCH_ServingCellConfig__ext2O__Format.

Definition PDSCH_ServingCellConfig__ext2__check_all_none (b : PDSCH_ServingCellConfig__ext2O__Type) : bool :=
match b with 
  | make__PDSCH_ServingCellConfig__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition PDSCH_ServingCellConfig__ext2__Format : T_Format PDSCH_ServingCellConfig__ext2__Type PDSCH_ServingCellConfig__ext2__cond :=
  restrict_add_format PDSCH_ServingCellConfig__ext2__check_all_none PDSCH_ServingCellConfig__ext2O__Format.

Opaque PDSCH_ServingCellConfig__ext2__cond PDSCH_ServingCellConfig__ext2__Format.


Definition PDSCH_ServingCellConfig__root_Format_Type := Eval cbn in seq_format_prod PDSCH_ServingCellConfig__root_list.
Definition PDSCH_ServingCellConfig__root_Format_list : PDSCH_ServingCellConfig__root_Format_Type :=
  (PDSCH_ServingCellConfig__codeBlockGroupTransmission__Format, (PDSCH_ServingCellConfig__xOverhead__Format, (PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH__Format, (ServCellIndex__Format, unit_format)))).

Definition PDSCH_ServingCellConfig__ext_Format_Type := Eval cbn in get_formats PDSCH_ServingCellConfig__ext_list.
Definition PDSCH_ServingCellConfig__ext_Format_list : PDSCH_ServingCellConfig__ext_Format_Type :=
  (PDSCH_ServingCellConfig__ext0__Format, (PDSCH_ServingCellConfig__ext1__Format, (PDSCH_ServingCellConfig__ext2__Format, unit__Format))).

Definition PDSCH_ServingCellConfig__list_type : Set := (seq_type PDSCH_ServingCellConfig__root_list) * (seq_ext_type PDSCH_ServingCellConfig__ext_list).
Definition PDSCH_ServingCellConfig__list_cond (z : PDSCH_ServingCellConfig__list_type) : Prop :=
        (seq_cond PDSCH_ServingCellConfig__root_list (fst z)) /\ (seq_ext_cond PDSCH_ServingCellConfig__ext_list (snd z)).
Definition PDSCH_ServingCellConfig__list_format : T_Format PDSCH_ServingCellConfig__list_type PDSCH_ServingCellConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PDSCH_ServingCellConfig__root_list PDSCH_ServingCellConfig__root_Format_list PDSCH_ServingCellConfig__ext_list PDSCH_ServingCellConfig__ext_Format_list.

Opaque PDSCH_ServingCellConfig__list_format.
Definition PDSCH_ServingCellConfig__F1 (z : PDSCH_ServingCellConfig__Type) : PDSCH_ServingCellConfig__list_type :=
  (((PDSCH_ServingCellConfig__codeBlockGroupTransmission z, (PDSCH_ServingCellConfig__xOverhead z, (PDSCH_ServingCellConfig__nrofHARQ_ProcessesForPDSCH z, (PDSCH_ServingCellConfig__pucch_Cell z, tt))))), (
(PDSCH_ServingCellConfig__ext0 z, (PDSCH_ServingCellConfig__ext1 z, (PDSCH_ServingCellConfig__ext2 z, tt))))).
Definition PDSCH_ServingCellConfig__F2 (y : PDSCH_ServingCellConfig__list_type) : PDSCH_ServingCellConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, (i2, _))))=>
    make__PDSCH_ServingCellConfig__Type j0 j1 j2 j3 i0 i1 i2
  end.
Definition PDSCH_ServingCellConfig__helper1 : (forall a : PDSCH_ServingCellConfig__Type, PDSCH_ServingCellConfig__cond a -> PDSCH_ServingCellConfig__list_cond (PDSCH_ServingCellConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDSCH_ServingCellConfig__helper2 : (forall a : PDSCH_ServingCellConfig__Type, PDSCH_ServingCellConfig__F2 (PDSCH_ServingCellConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDSCH_ServingCellConfig__helper3 : (forall b : PDSCH_ServingCellConfig__list_type, PDSCH_ServingCellConfig__list_cond b -> PDSCH_ServingCellConfig__cond (PDSCH_ServingCellConfig__F2 b) /\ PDSCH_ServingCellConfig__F1 (PDSCH_ServingCellConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDSCH_ServingCellConfig__cond, PDSCH_ServingCellConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDSCH_ServingCellConfig__Format : T_Format PDSCH_ServingCellConfig__Type PDSCH_ServingCellConfig__cond :=
 proj2_format PDSCH_ServingCellConfig__cond PDSCH_ServingCellConfig__list_format  PDSCH_ServingCellConfig__F1 PDSCH_ServingCellConfig__F2 PDSCH_ServingCellConfig__helper1 PDSCH_ServingCellConfig__helper2 PDSCH_ServingCellConfig__helper3.

Opaque PDSCH_ServingCellConfig__cond PDSCH_ServingCellConfig__Format.

