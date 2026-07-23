Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.PUSCH_CodeBlockGroupTransmission.
Definition PUSCH_ServingCellConfig__codeBlockGroupTransmission__Type := SetupRelease__Type PUSCH_CodeBlockGroupTransmission__Type.
Definition PUSCH_ServingCellConfig__codeBlockGroupTransmission__cond := SetupRelease__cond _ PUSCH_CodeBlockGroupTransmission__cond.
Definition PUSCH_ServingCellConfig__codeBlockGroupTransmission__Format : T_Format PUSCH_ServingCellConfig__codeBlockGroupTransmission__Type PUSCH_ServingCellConfig__codeBlockGroupTransmission__cond := SetupRelease__Format _ _ PUSCH_CodeBlockGroupTransmission__Format.
Opaque PUSCH_ServingCellConfig__codeBlockGroupTransmission__cond PUSCH_ServingCellConfig__codeBlockGroupTransmission__Format.

Inductive PUSCH_ServingCellConfig__rateMatching__Type : Set :=
 | PUSCH_ServingCellConfig__rateMatching__limitedBufferRM
.
Definition PUSCH_ServingCellConfig__rateMatching__cond := (fun (_ : PUSCH_ServingCellConfig__rateMatching__Type) => True).
Lemma PUSCH_ServingCellConfig__rateMatching__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_ServingCellConfig__rateMatching__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_ServingCellConfig__rateMatching__nat__helper.

Definition PUSCH_ServingCellConfig__rateMatching__F1 t :=
  match t with
  | PUSCH_ServingCellConfig__rateMatching__limitedBufferRM => 0
  end.
Definition PUSCH_ServingCellConfig__rateMatching__F2 n :=
  match n with
  | 0 => PUSCH_ServingCellConfig__rateMatching__limitedBufferRM
  | _ => PUSCH_ServingCellConfig__rateMatching__limitedBufferRM
  end.
Lemma PUSCH_ServingCellConfig__rateMatching__F1F2 : forall x : PUSCH_ServingCellConfig__rateMatching__Type, (PUSCH_ServingCellConfig__rateMatching__F1 x <= 0) /\ PUSCH_ServingCellConfig__rateMatching__F2 (PUSCH_ServingCellConfig__rateMatching__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_ServingCellConfig__rateMatching__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_ServingCellConfig__rateMatching__F1 (PUSCH_ServingCellConfig__rateMatching__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_ServingCellConfig__xOverhead__Type : Set :=
 | PUSCH_ServingCellConfig__xOverhead__xoh6
 | PUSCH_ServingCellConfig__xOverhead__xoh12
 | PUSCH_ServingCellConfig__xOverhead__xoh18
.
Definition PUSCH_ServingCellConfig__xOverhead__cond := (fun (_ : PUSCH_ServingCellConfig__xOverhead__Type) => True).
Lemma PUSCH_ServingCellConfig__xOverhead__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_ServingCellConfig__xOverhead__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUSCH_ServingCellConfig__xOverhead__nat__helper.

Definition PUSCH_ServingCellConfig__xOverhead__F1 t :=
  match t with
  | PUSCH_ServingCellConfig__xOverhead__xoh6 => 0
  | PUSCH_ServingCellConfig__xOverhead__xoh12 => 1
  | PUSCH_ServingCellConfig__xOverhead__xoh18 => 2
  end.
Definition PUSCH_ServingCellConfig__xOverhead__F2 n :=
  match n with
  | 0 => PUSCH_ServingCellConfig__xOverhead__xoh6
  | 1 => PUSCH_ServingCellConfig__xOverhead__xoh12
  | 2 => PUSCH_ServingCellConfig__xOverhead__xoh18
  | _ => PUSCH_ServingCellConfig__xOverhead__xoh6
  end.
Lemma PUSCH_ServingCellConfig__xOverhead__F1F2 : forall x : PUSCH_ServingCellConfig__xOverhead__Type, (PUSCH_ServingCellConfig__xOverhead__F1 x <= 2) /\ PUSCH_ServingCellConfig__xOverhead__F2 (PUSCH_ServingCellConfig__xOverhead__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_ServingCellConfig__xOverhead__F2F1 : forall (y : nat) (H : y <= 2), PUSCH_ServingCellConfig__xOverhead__F1 (PUSCH_ServingCellConfig__xOverhead__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__Type := Z.
Definition PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond := (fun z => (1 <= z <= 4)%Z).
Record PUSCH_ServingCellConfig__ext0O__Type : Set :=
  make__PUSCH_ServingCellConfig__ext0O__Type {
    PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers : option Z ;
    PUSCH_ServingCellConfig__ext0O__processingType2Enabled : option bool ;
}.
Definition PUSCH_ServingCellConfig__ext0O__list := (
 Opt Z PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond ::
 Opt bool (fun _ => True) ::
 nil).
Definition PUSCH_ServingCellConfig__ext0O__cond z := 
  opt_cond PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond (PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers z) /\
  opt_cond (fun _ => True) (PUSCH_ServingCellConfig__ext0O__processingType2Enabled z) /\
  True.

Definition PUSCH_ServingCellConfig__ext0__Type := PUSCH_ServingCellConfig__ext0O__Type.
Definition PUSCH_ServingCellConfig__ext0__cond := PUSCH_ServingCellConfig__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.MaxMIMO_LayersDCI_0_2_r16.
Definition PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__Type := SetupRelease__Type MaxMIMO_LayersDCI_0_2_r16__Type.
Definition PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__cond := SetupRelease__cond _ MaxMIMO_LayersDCI_0_2_r16__cond.
Definition PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__Format : T_Format PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__Type PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__cond := SetupRelease__Format _ _ MaxMIMO_LayersDCI_0_2_r16__Format.
Opaque PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__cond PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__Format.

Record PUSCH_ServingCellConfig__ext1O__Type : Set :=
  make__PUSCH_ServingCellConfig__ext1O__Type {
    PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16 : option PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__Type ;
}.
Definition PUSCH_ServingCellConfig__ext1O__list := (
 Opt PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__Type PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__cond ::
 nil).
Definition PUSCH_ServingCellConfig__ext1O__cond z := 
  opt_cond PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__cond (PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16 z) /\
  True.

Definition PUSCH_ServingCellConfig__ext1__Type := PUSCH_ServingCellConfig__ext1O__Type.
Definition PUSCH_ServingCellConfig__ext1__cond := PUSCH_ServingCellConfig__ext1O__cond.

Inductive PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Type : Set :=
 | PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__n32
.
Definition PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__cond := (fun (_ : PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Type) => True).
Lemma PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__nat__helper.

Definition PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F1 t :=
  match t with
  | PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__n32 => 0
  end.
Definition PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F2 n :=
  match n with
  | 0 => PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__n32
  | _ => PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__n32
  end.
Lemma PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F1F2 : forall x : PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Type, (PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F1 x <= 0) /\ PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F2 (PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F1 (PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.UplinkHARQ_mode_r17.
Definition PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__Type := SetupRelease__Type UplinkHARQ_mode_r17__Type.
Definition PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__cond := SetupRelease__cond _ UplinkHARQ_mode_r17__cond.
Definition PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__Format : T_Format PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__Type PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__cond := SetupRelease__Format _ _ UplinkHARQ_mode_r17__Format.
Opaque PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__cond PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__Format.

Record PUSCH_ServingCellConfig__ext2O__Type : Set :=
  make__PUSCH_ServingCellConfig__ext2O__Type {
    PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17 : option PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Type ;
    PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17 : option PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__Type ;
}.
Definition PUSCH_ServingCellConfig__ext2O__list := (
 Opt PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Type PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__cond ::
 Opt PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__Type PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__cond ::
 nil).
Definition PUSCH_ServingCellConfig__ext2O__cond z := 
  opt_cond PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__cond (PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17 z) /\
  opt_cond PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__cond (PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17 z) /\
  True.

Definition PUSCH_ServingCellConfig__ext2__Type := PUSCH_ServingCellConfig__ext2O__Type.
Definition PUSCH_ServingCellConfig__ext2__cond := PUSCH_ServingCellConfig__ext2O__cond.

Record PUSCH_ServingCellConfig__Type : Set :=
  make__PUSCH_ServingCellConfig__Type {
    PUSCH_ServingCellConfig__codeBlockGroupTransmission : option PUSCH_ServingCellConfig__codeBlockGroupTransmission__Type ;
    PUSCH_ServingCellConfig__rateMatching : option PUSCH_ServingCellConfig__rateMatching__Type ;
    PUSCH_ServingCellConfig__xOverhead : option PUSCH_ServingCellConfig__xOverhead__Type ;
    PUSCH_ServingCellConfig__ext0 : option PUSCH_ServingCellConfig__ext0__Type ;
    PUSCH_ServingCellConfig__ext1 : option PUSCH_ServingCellConfig__ext1__Type ;
    PUSCH_ServingCellConfig__ext2 : option PUSCH_ServingCellConfig__ext2__Type ;
}.
Definition PUSCH_ServingCellConfig__root_list : list seq_elem := (
 Opt PUSCH_ServingCellConfig__codeBlockGroupTransmission__Type PUSCH_ServingCellConfig__codeBlockGroupTransmission__cond ::
 Opt PUSCH_ServingCellConfig__rateMatching__Type PUSCH_ServingCellConfig__rateMatching__cond ::
 Opt PUSCH_ServingCellConfig__xOverhead__Type PUSCH_ServingCellConfig__xOverhead__cond ::
 nil).
Definition PUSCH_ServingCellConfig__ext_list : list typ := (
  typ_cons PUSCH_ServingCellConfig__ext0__Type PUSCH_ServingCellConfig__ext0__cond ::
  typ_cons PUSCH_ServingCellConfig__ext1__Type PUSCH_ServingCellConfig__ext1__cond ::
  typ_cons PUSCH_ServingCellConfig__ext2__Type PUSCH_ServingCellConfig__ext2__cond ::
  nil).
Definition PUSCH_ServingCellConfig__cond (z : PUSCH_ServingCellConfig__Type) := 
(  opt_cond PUSCH_ServingCellConfig__codeBlockGroupTransmission__cond (PUSCH_ServingCellConfig__codeBlockGroupTransmission z) /\
  opt_cond PUSCH_ServingCellConfig__rateMatching__cond (PUSCH_ServingCellConfig__rateMatching z) /\
  opt_cond PUSCH_ServingCellConfig__xOverhead__cond (PUSCH_ServingCellConfig__xOverhead z) /\
  True) /\ 
(  opt_cond PUSCH_ServingCellConfig__ext0__cond (PUSCH_ServingCellConfig__ext0 z) /\
  opt_cond PUSCH_ServingCellConfig__ext1__cond (PUSCH_ServingCellConfig__ext1 z) /\
  opt_cond PUSCH_ServingCellConfig__ext2__cond (PUSCH_ServingCellConfig__ext2 z) /\
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
Opaque PUSCH_ServingCellConfig__codeBlockGroupTransmission__cond PUSCH_ServingCellConfig__codeBlockGroupTransmission__Format.

Definition PUSCH_ServingCellConfig__rateMatching__Format : T_Format PUSCH_ServingCellConfig__rateMatching__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_ServingCellConfig__rateMatching__nat__Format PUSCH_ServingCellConfig__rateMatching__F1 PUSCH_ServingCellConfig__rateMatching__F2 PUSCH_ServingCellConfig__rateMatching__F1F2 PUSCH_ServingCellConfig__rateMatching__F2F1.

Opaque PUSCH_ServingCellConfig__rateMatching__cond PUSCH_ServingCellConfig__rateMatching__Format.

Definition PUSCH_ServingCellConfig__xOverhead__Format : T_Format PUSCH_ServingCellConfig__xOverhead__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_ServingCellConfig__xOverhead__nat__Format PUSCH_ServingCellConfig__xOverhead__F1 PUSCH_ServingCellConfig__xOverhead__F2 PUSCH_ServingCellConfig__xOverhead__F1F2 PUSCH_ServingCellConfig__xOverhead__F2F1.

Opaque PUSCH_ServingCellConfig__xOverhead__cond PUSCH_ServingCellConfig__xOverhead__Format.

Definition PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__Format : T_Format Z PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond :=
 ranged_int_format (1) (4) PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper1 PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__helper2.

Opaque PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__cond PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__Format.


Definition PUSCH_ServingCellConfig__ext0O__Format_Type := Eval cbn in seq_format_prod PUSCH_ServingCellConfig__ext0O__list.
Definition PUSCH_ServingCellConfig__ext0O__Format_list : PUSCH_ServingCellConfig__ext0O__Format_Type :=
  (PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers__Format, (bool__Format, unit_format)).
Definition PUSCH_ServingCellConfig__ext0O__list__Format := (*Eval compute in *) seq_format PUSCH_ServingCellConfig__ext0O__list PUSCH_ServingCellConfig__ext0O__Format_list.
Definition PUSCH_ServingCellConfig__ext0O__F1 z :=
  (PUSCH_ServingCellConfig__ext0O__maxMIMO_Layers z, (PUSCH_ServingCellConfig__ext0O__processingType2Enabled z, tt)).
Definition PUSCH_ServingCellConfig__ext0O__F2 (y : seq_type PUSCH_ServingCellConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUSCH_ServingCellConfig__ext0O__Type i0 i1
  end.
Lemma PUSCH_ServingCellConfig__ext0O__F1F2_cond (z : PUSCH_ServingCellConfig__ext0O__Type)
  : PUSCH_ServingCellConfig__ext0O__cond z ->
  (seq_cond PUSCH_ServingCellConfig__ext0O__list (PUSCH_ServingCellConfig__ext0O__F1 z)).
intro H. unfold PUSCH_ServingCellConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma PUSCH_ServingCellConfig__ext0O__F1F2_cond2 (z : PUSCH_ServingCellConfig__ext0O__Type)
 : PUSCH_ServingCellConfig__ext0O__F2 (PUSCH_ServingCellConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_ServingCellConfig__ext0O__F2F1_cond (y : seq_type PUSCH_ServingCellConfig__ext0O__list)
  : seq_cond PUSCH_ServingCellConfig__ext0O__list y ->
 (PUSCH_ServingCellConfig__ext0O__cond (PUSCH_ServingCellConfig__ext0O__F2 y)) /\  PUSCH_ServingCellConfig__ext0O__F1 (PUSCH_ServingCellConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_ServingCellConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUSCH_ServingCellConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_ServingCellConfig__ext0O__Format : T_Format PUSCH_ServingCellConfig__ext0O__Type PUSCH_ServingCellConfig__ext0O__cond :=
        proj2_format  PUSCH_ServingCellConfig__ext0O__cond PUSCH_ServingCellConfig__ext0O__list__Format
    PUSCH_ServingCellConfig__ext0O__F1 PUSCH_ServingCellConfig__ext0O__F2 PUSCH_ServingCellConfig__ext0O__F1F2_cond  PUSCH_ServingCellConfig__ext0O__F1F2_cond2 PUSCH_ServingCellConfig__ext0O__F2F1_cond.
Opaque PUSCH_ServingCellConfig__ext0O__cond PUSCH_ServingCellConfig__ext0O__Format.

Definition PUSCH_ServingCellConfig__ext0__check_all_none (b : PUSCH_ServingCellConfig__ext0O__Type) : bool :=
match b with 
  | make__PUSCH_ServingCellConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition PUSCH_ServingCellConfig__ext0__Format : T_Format PUSCH_ServingCellConfig__ext0__Type PUSCH_ServingCellConfig__ext0__cond :=
  restrict_add_format PUSCH_ServingCellConfig__ext0__check_all_none PUSCH_ServingCellConfig__ext0O__Format.

Opaque PUSCH_ServingCellConfig__ext0__cond PUSCH_ServingCellConfig__ext0__Format.

Opaque PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__cond PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__Format.


Definition PUSCH_ServingCellConfig__ext1O__Format_Type := Eval cbn in seq_format_prod PUSCH_ServingCellConfig__ext1O__list.
Definition PUSCH_ServingCellConfig__ext1O__Format_list : PUSCH_ServingCellConfig__ext1O__Format_Type :=
  (PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16__Format, unit_format).
Definition PUSCH_ServingCellConfig__ext1O__list__Format := (*Eval compute in *) seq_format PUSCH_ServingCellConfig__ext1O__list PUSCH_ServingCellConfig__ext1O__Format_list.
Definition PUSCH_ServingCellConfig__ext1O__F1 z :=
  (PUSCH_ServingCellConfig__ext1O__maxMIMO_LayersDCI_0_2_r16 z, tt).
Definition PUSCH_ServingCellConfig__ext1O__F2 (y : seq_type PUSCH_ServingCellConfig__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__PUSCH_ServingCellConfig__ext1O__Type i0
  end.
Lemma PUSCH_ServingCellConfig__ext1O__F1F2_cond (z : PUSCH_ServingCellConfig__ext1O__Type)
  : PUSCH_ServingCellConfig__ext1O__cond z ->
  (seq_cond PUSCH_ServingCellConfig__ext1O__list (PUSCH_ServingCellConfig__ext1O__F1 z)).
intro H. unfold PUSCH_ServingCellConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma PUSCH_ServingCellConfig__ext1O__F1F2_cond2 (z : PUSCH_ServingCellConfig__ext1O__Type)
 : PUSCH_ServingCellConfig__ext1O__F2 (PUSCH_ServingCellConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_ServingCellConfig__ext1O__F2F1_cond (y : seq_type PUSCH_ServingCellConfig__ext1O__list)
  : seq_cond PUSCH_ServingCellConfig__ext1O__list y ->
 (PUSCH_ServingCellConfig__ext1O__cond (PUSCH_ServingCellConfig__ext1O__F2 y)) /\  PUSCH_ServingCellConfig__ext1O__F1 (PUSCH_ServingCellConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_ServingCellConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold PUSCH_ServingCellConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_ServingCellConfig__ext1O__Format : T_Format PUSCH_ServingCellConfig__ext1O__Type PUSCH_ServingCellConfig__ext1O__cond :=
        proj2_format  PUSCH_ServingCellConfig__ext1O__cond PUSCH_ServingCellConfig__ext1O__list__Format
    PUSCH_ServingCellConfig__ext1O__F1 PUSCH_ServingCellConfig__ext1O__F2 PUSCH_ServingCellConfig__ext1O__F1F2_cond  PUSCH_ServingCellConfig__ext1O__F1F2_cond2 PUSCH_ServingCellConfig__ext1O__F2F1_cond.
Opaque PUSCH_ServingCellConfig__ext1O__cond PUSCH_ServingCellConfig__ext1O__Format.

Definition PUSCH_ServingCellConfig__ext1__check_all_none (b : PUSCH_ServingCellConfig__ext1O__Type) : bool :=
match b with 
  | make__PUSCH_ServingCellConfig__ext1O__Type None  => false 
  | _ => true 
 end.
Definition PUSCH_ServingCellConfig__ext1__Format : T_Format PUSCH_ServingCellConfig__ext1__Type PUSCH_ServingCellConfig__ext1__cond :=
  restrict_add_format PUSCH_ServingCellConfig__ext1__check_all_none PUSCH_ServingCellConfig__ext1O__Format.

Opaque PUSCH_ServingCellConfig__ext1__cond PUSCH_ServingCellConfig__ext1__Format.

Definition PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Format : T_Format PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__nat__Format PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F1 PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F2 PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F1F2 PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__F2F1.

Opaque PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__cond PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Format.

Opaque PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__cond PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__Format.


Definition PUSCH_ServingCellConfig__ext2O__Format_Type := Eval cbn in seq_format_prod PUSCH_ServingCellConfig__ext2O__list.
Definition PUSCH_ServingCellConfig__ext2O__Format_list : PUSCH_ServingCellConfig__ext2O__Format_Type :=
  (PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17__Format, (PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17__Format, unit_format)).
Definition PUSCH_ServingCellConfig__ext2O__list__Format := (*Eval compute in *) seq_format PUSCH_ServingCellConfig__ext2O__list PUSCH_ServingCellConfig__ext2O__Format_list.
Definition PUSCH_ServingCellConfig__ext2O__F1 z :=
  (PUSCH_ServingCellConfig__ext2O__nrofHARQ_ProcessesForPUSCH_r17 z, (PUSCH_ServingCellConfig__ext2O__uplinkHARQ_mode_r17 z, tt)).
Definition PUSCH_ServingCellConfig__ext2O__F2 (y : seq_type PUSCH_ServingCellConfig__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUSCH_ServingCellConfig__ext2O__Type i0 i1
  end.
Lemma PUSCH_ServingCellConfig__ext2O__F1F2_cond (z : PUSCH_ServingCellConfig__ext2O__Type)
  : PUSCH_ServingCellConfig__ext2O__cond z ->
  (seq_cond PUSCH_ServingCellConfig__ext2O__list (PUSCH_ServingCellConfig__ext2O__F1 z)).
intro H. unfold PUSCH_ServingCellConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma PUSCH_ServingCellConfig__ext2O__F1F2_cond2 (z : PUSCH_ServingCellConfig__ext2O__Type)
 : PUSCH_ServingCellConfig__ext2O__F2 (PUSCH_ServingCellConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_ServingCellConfig__ext2O__F2F1_cond (y : seq_type PUSCH_ServingCellConfig__ext2O__list)
  : seq_cond PUSCH_ServingCellConfig__ext2O__list y ->
 (PUSCH_ServingCellConfig__ext2O__cond (PUSCH_ServingCellConfig__ext2O__F2 y)) /\  PUSCH_ServingCellConfig__ext2O__F1 (PUSCH_ServingCellConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_ServingCellConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold PUSCH_ServingCellConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_ServingCellConfig__ext2O__Format : T_Format PUSCH_ServingCellConfig__ext2O__Type PUSCH_ServingCellConfig__ext2O__cond :=
        proj2_format  PUSCH_ServingCellConfig__ext2O__cond PUSCH_ServingCellConfig__ext2O__list__Format
    PUSCH_ServingCellConfig__ext2O__F1 PUSCH_ServingCellConfig__ext2O__F2 PUSCH_ServingCellConfig__ext2O__F1F2_cond  PUSCH_ServingCellConfig__ext2O__F1F2_cond2 PUSCH_ServingCellConfig__ext2O__F2F1_cond.
Opaque PUSCH_ServingCellConfig__ext2O__cond PUSCH_ServingCellConfig__ext2O__Format.

Definition PUSCH_ServingCellConfig__ext2__check_all_none (b : PUSCH_ServingCellConfig__ext2O__Type) : bool :=
match b with 
  | make__PUSCH_ServingCellConfig__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition PUSCH_ServingCellConfig__ext2__Format : T_Format PUSCH_ServingCellConfig__ext2__Type PUSCH_ServingCellConfig__ext2__cond :=
  restrict_add_format PUSCH_ServingCellConfig__ext2__check_all_none PUSCH_ServingCellConfig__ext2O__Format.

Opaque PUSCH_ServingCellConfig__ext2__cond PUSCH_ServingCellConfig__ext2__Format.


Definition PUSCH_ServingCellConfig__root_Format_Type := Eval cbn in seq_format_prod PUSCH_ServingCellConfig__root_list.
Definition PUSCH_ServingCellConfig__root_Format_list : PUSCH_ServingCellConfig__root_Format_Type :=
  (PUSCH_ServingCellConfig__codeBlockGroupTransmission__Format, (PUSCH_ServingCellConfig__rateMatching__Format, (PUSCH_ServingCellConfig__xOverhead__Format, unit_format))).

Definition PUSCH_ServingCellConfig__ext_Format_Type := Eval cbn in get_formats PUSCH_ServingCellConfig__ext_list.
Definition PUSCH_ServingCellConfig__ext_Format_list : PUSCH_ServingCellConfig__ext_Format_Type :=
  (PUSCH_ServingCellConfig__ext0__Format, (PUSCH_ServingCellConfig__ext1__Format, (PUSCH_ServingCellConfig__ext2__Format, unit__Format))).

Definition PUSCH_ServingCellConfig__list_type : Set := (seq_type PUSCH_ServingCellConfig__root_list) * (seq_ext_type PUSCH_ServingCellConfig__ext_list).
Definition PUSCH_ServingCellConfig__list_cond (z : PUSCH_ServingCellConfig__list_type) : Prop :=
        (seq_cond PUSCH_ServingCellConfig__root_list (fst z)) /\ (seq_ext_cond PUSCH_ServingCellConfig__ext_list (snd z)).
Definition PUSCH_ServingCellConfig__list_format : T_Format PUSCH_ServingCellConfig__list_type PUSCH_ServingCellConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PUSCH_ServingCellConfig__root_list PUSCH_ServingCellConfig__root_Format_list PUSCH_ServingCellConfig__ext_list PUSCH_ServingCellConfig__ext_Format_list.

Opaque PUSCH_ServingCellConfig__list_format.
Definition PUSCH_ServingCellConfig__F1 (z : PUSCH_ServingCellConfig__Type) : PUSCH_ServingCellConfig__list_type :=
  (((PUSCH_ServingCellConfig__codeBlockGroupTransmission z, (PUSCH_ServingCellConfig__rateMatching z, (PUSCH_ServingCellConfig__xOverhead z, tt)))), (
(PUSCH_ServingCellConfig__ext0 z, (PUSCH_ServingCellConfig__ext1 z, (PUSCH_ServingCellConfig__ext2 z, tt))))).
Definition PUSCH_ServingCellConfig__F2 (y : PUSCH_ServingCellConfig__list_type) : PUSCH_ServingCellConfig__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, _))))=>
    make__PUSCH_ServingCellConfig__Type j0 j1 j2 i0 i1 i2
  end.
Definition PUSCH_ServingCellConfig__helper1 : (forall a : PUSCH_ServingCellConfig__Type, PUSCH_ServingCellConfig__cond a -> PUSCH_ServingCellConfig__list_cond (PUSCH_ServingCellConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUSCH_ServingCellConfig__helper2 : (forall a : PUSCH_ServingCellConfig__Type, PUSCH_ServingCellConfig__F2 (PUSCH_ServingCellConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUSCH_ServingCellConfig__helper3 : (forall b : PUSCH_ServingCellConfig__list_type, PUSCH_ServingCellConfig__list_cond b -> PUSCH_ServingCellConfig__cond (PUSCH_ServingCellConfig__F2 b) /\ PUSCH_ServingCellConfig__F1 (PUSCH_ServingCellConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUSCH_ServingCellConfig__cond, PUSCH_ServingCellConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUSCH_ServingCellConfig__Format : T_Format PUSCH_ServingCellConfig__Type PUSCH_ServingCellConfig__cond :=
 proj2_format PUSCH_ServingCellConfig__cond PUSCH_ServingCellConfig__list_format  PUSCH_ServingCellConfig__F1 PUSCH_ServingCellConfig__F2 PUSCH_ServingCellConfig__helper1 PUSCH_ServingCellConfig__helper2 PUSCH_ServingCellConfig__helper3.

Opaque PUSCH_ServingCellConfig__cond PUSCH_ServingCellConfig__Format.

