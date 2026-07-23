Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Inductive SSB_Configuration_r16__halfFrameIndex_r16__Type : Set :=
 | SSB_Configuration_r16__halfFrameIndex_r16__zero
 | SSB_Configuration_r16__halfFrameIndex_r16__one
.
Definition SSB_Configuration_r16__halfFrameIndex_r16__cond := (fun (_ : SSB_Configuration_r16__halfFrameIndex_r16__Type) => True).
Lemma SSB_Configuration_r16__halfFrameIndex_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SSB_Configuration_r16__halfFrameIndex_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SSB_Configuration_r16__halfFrameIndex_r16__nat__helper.

Definition SSB_Configuration_r16__halfFrameIndex_r16__F1 t :=
  match t with
  | SSB_Configuration_r16__halfFrameIndex_r16__zero => 0
  | SSB_Configuration_r16__halfFrameIndex_r16__one => 1
  end.
Definition SSB_Configuration_r16__halfFrameIndex_r16__F2 n :=
  match n with
  | 0 => SSB_Configuration_r16__halfFrameIndex_r16__zero
  | 1 => SSB_Configuration_r16__halfFrameIndex_r16__one
  | _ => SSB_Configuration_r16__halfFrameIndex_r16__zero
  end.
Lemma SSB_Configuration_r16__halfFrameIndex_r16__F1F2 : forall x : SSB_Configuration_r16__halfFrameIndex_r16__Type, (SSB_Configuration_r16__halfFrameIndex_r16__F1 x <= 1) /\ SSB_Configuration_r16__halfFrameIndex_r16__F2 (SSB_Configuration_r16__halfFrameIndex_r16__F1 x) = x. imp_solve. Qed.
Lemma SSB_Configuration_r16__halfFrameIndex_r16__F2F1 : forall (y : nat) (H : y <= 1), SSB_Configuration_r16__halfFrameIndex_r16__F1 (SSB_Configuration_r16__halfFrameIndex_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Inductive SSB_Configuration_r16__ssb_Periodicity_r16__Type : Set :=
 | SSB_Configuration_r16__ssb_Periodicity_r16__ms5
 | SSB_Configuration_r16__ssb_Periodicity_r16__ms10
 | SSB_Configuration_r16__ssb_Periodicity_r16__ms20
 | SSB_Configuration_r16__ssb_Periodicity_r16__ms40
 | SSB_Configuration_r16__ssb_Periodicity_r16__ms80
 | SSB_Configuration_r16__ssb_Periodicity_r16__ms160
 | SSB_Configuration_r16__ssb_Periodicity_r16__spare2
 | SSB_Configuration_r16__ssb_Periodicity_r16__spare1
.
Definition SSB_Configuration_r16__ssb_Periodicity_r16__cond := (fun (_ : SSB_Configuration_r16__ssb_Periodicity_r16__Type) => True).
Lemma SSB_Configuration_r16__ssb_Periodicity_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SSB_Configuration_r16__ssb_Periodicity_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SSB_Configuration_r16__ssb_Periodicity_r16__nat__helper.

Definition SSB_Configuration_r16__ssb_Periodicity_r16__F1 t :=
  match t with
  | SSB_Configuration_r16__ssb_Periodicity_r16__ms5 => 0
  | SSB_Configuration_r16__ssb_Periodicity_r16__ms10 => 1
  | SSB_Configuration_r16__ssb_Periodicity_r16__ms20 => 2
  | SSB_Configuration_r16__ssb_Periodicity_r16__ms40 => 3
  | SSB_Configuration_r16__ssb_Periodicity_r16__ms80 => 4
  | SSB_Configuration_r16__ssb_Periodicity_r16__ms160 => 5
  | SSB_Configuration_r16__ssb_Periodicity_r16__spare2 => 6
  | SSB_Configuration_r16__ssb_Periodicity_r16__spare1 => 7
  end.
Definition SSB_Configuration_r16__ssb_Periodicity_r16__F2 n :=
  match n with
  | 0 => SSB_Configuration_r16__ssb_Periodicity_r16__ms5
  | 1 => SSB_Configuration_r16__ssb_Periodicity_r16__ms10
  | 2 => SSB_Configuration_r16__ssb_Periodicity_r16__ms20
  | 3 => SSB_Configuration_r16__ssb_Periodicity_r16__ms40
  | 4 => SSB_Configuration_r16__ssb_Periodicity_r16__ms80
  | 5 => SSB_Configuration_r16__ssb_Periodicity_r16__ms160
  | 6 => SSB_Configuration_r16__ssb_Periodicity_r16__spare2
  | 7 => SSB_Configuration_r16__ssb_Periodicity_r16__spare1
  | _ => SSB_Configuration_r16__ssb_Periodicity_r16__ms5
  end.
Lemma SSB_Configuration_r16__ssb_Periodicity_r16__F1F2 : forall x : SSB_Configuration_r16__ssb_Periodicity_r16__Type, (SSB_Configuration_r16__ssb_Periodicity_r16__F1 x <= 7) /\ SSB_Configuration_r16__ssb_Periodicity_r16__F2 (SSB_Configuration_r16__ssb_Periodicity_r16__F1 x) = x. imp_solve. Qed.
Lemma SSB_Configuration_r16__ssb_Periodicity_r16__F2F1 : forall (y : nat) (H : y <= 7), SSB_Configuration_r16__ssb_Periodicity_r16__F1 (SSB_Configuration_r16__ssb_Periodicity_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__Type := Z.
Definition SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__Type := Z.
Definition SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__cond := (fun z => (0 <= z <= 9)%Z).
Record SSB_Configuration_r16__sfn0_Offset_r16__Type : Set :=
  make__SSB_Configuration_r16__sfn0_Offset_r16__Type {
    SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16 : Z ;
    SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16 : option Z ;
}.
Definition SSB_Configuration_r16__sfn0_Offset_r16__list := (
 Nor Z SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__cond ::
 Opt Z SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__cond ::
 nil).
Definition SSB_Configuration_r16__sfn0_Offset_r16__cond z := 
  SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__cond (SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16 z) /\
  opt_cond SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__cond (SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16 z) /\
  True.

Lemma SSB_Configuration_r16__sfn_SSB_Offset_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SSB_Configuration_r16__sfn_SSB_Offset_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_Configuration_r16__sfn_SSB_Offset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_Configuration_r16__sfn_SSB_Offset_r16__Type := Z.
Definition SSB_Configuration_r16__sfn_SSB_Offset_r16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma SSB_Configuration_r16__ss_PBCH_BlockPower_r16__helper1 : (-60 <= 50)%Z.  lia. Qed.
Lemma SSB_Configuration_r16__ss_PBCH_BlockPower_r16__helper2 : to_bit_sz (Z.to_nat (50 - -60)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (50 - -60))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_Configuration_r16__ss_PBCH_BlockPower_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_Configuration_r16__ss_PBCH_BlockPower_r16__Type := Z.
Definition SSB_Configuration_r16__ss_PBCH_BlockPower_r16__cond := (fun z => (-60 <= z <= 50)%Z).
Record SSB_Configuration_r16__Type : Set :=
  make__SSB_Configuration_r16__Type {
    SSB_Configuration_r16__ssb_Freq_r16 : ARFCN_ValueNR__Type ;
    SSB_Configuration_r16__halfFrameIndex_r16 : SSB_Configuration_r16__halfFrameIndex_r16__Type ;
    SSB_Configuration_r16__ssbSubcarrierSpacing_r16 : SubcarrierSpacing__Type ;
    SSB_Configuration_r16__ssb_Periodicity_r16 : option SSB_Configuration_r16__ssb_Periodicity_r16__Type ;
    SSB_Configuration_r16__sfn0_Offset_r16 : option SSB_Configuration_r16__sfn0_Offset_r16__Type ;
    SSB_Configuration_r16__sfn_SSB_Offset_r16 : Z ;
    SSB_Configuration_r16__ss_PBCH_BlockPower_r16 : option Z ;
}.
Definition SSB_Configuration_r16__list := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor SSB_Configuration_r16__halfFrameIndex_r16__Type SSB_Configuration_r16__halfFrameIndex_r16__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt SSB_Configuration_r16__ssb_Periodicity_r16__Type SSB_Configuration_r16__ssb_Periodicity_r16__cond ::
 Opt SSB_Configuration_r16__sfn0_Offset_r16__Type SSB_Configuration_r16__sfn0_Offset_r16__cond ::
 Nor Z SSB_Configuration_r16__sfn_SSB_Offset_r16__cond ::
 Opt Z SSB_Configuration_r16__ss_PBCH_BlockPower_r16__cond ::
 nil).
Definition SSB_Configuration_r16__cond z := 
  ARFCN_ValueNR__cond (SSB_Configuration_r16__ssb_Freq_r16 z) /\
  SSB_Configuration_r16__halfFrameIndex_r16__cond (SSB_Configuration_r16__halfFrameIndex_r16 z) /\
  SubcarrierSpacing__cond (SSB_Configuration_r16__ssbSubcarrierSpacing_r16 z) /\
  opt_cond SSB_Configuration_r16__ssb_Periodicity_r16__cond (SSB_Configuration_r16__ssb_Periodicity_r16 z) /\
  opt_cond SSB_Configuration_r16__sfn0_Offset_r16__cond (SSB_Configuration_r16__sfn0_Offset_r16 z) /\
  SSB_Configuration_r16__sfn_SSB_Offset_r16__cond (SSB_Configuration_r16__sfn_SSB_Offset_r16 z) /\
  opt_cond SSB_Configuration_r16__ss_PBCH_BlockPower_r16__cond (SSB_Configuration_r16__ss_PBCH_BlockPower_r16 z) /\
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
Definition SSB_Configuration_r16__halfFrameIndex_r16__Format : T_Format SSB_Configuration_r16__halfFrameIndex_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SSB_Configuration_r16__halfFrameIndex_r16__nat__Format SSB_Configuration_r16__halfFrameIndex_r16__F1 SSB_Configuration_r16__halfFrameIndex_r16__F2 SSB_Configuration_r16__halfFrameIndex_r16__F1F2 SSB_Configuration_r16__halfFrameIndex_r16__F2F1.

Opaque SSB_Configuration_r16__halfFrameIndex_r16__cond SSB_Configuration_r16__halfFrameIndex_r16__Format.

Definition SSB_Configuration_r16__ssb_Periodicity_r16__Format : T_Format SSB_Configuration_r16__ssb_Periodicity_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SSB_Configuration_r16__ssb_Periodicity_r16__nat__Format SSB_Configuration_r16__ssb_Periodicity_r16__F1 SSB_Configuration_r16__ssb_Periodicity_r16__F2 SSB_Configuration_r16__ssb_Periodicity_r16__F1F2 SSB_Configuration_r16__ssb_Periodicity_r16__F2F1.

Opaque SSB_Configuration_r16__ssb_Periodicity_r16__cond SSB_Configuration_r16__ssb_Periodicity_r16__Format.

Definition SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__Format : T_Format Z SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__cond :=
 ranged_int_format (0) (1023) SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__helper1 SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__helper2.

Opaque SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__cond SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__Format.

Definition SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__Format : T_Format Z SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__cond :=
 ranged_int_format (0) (9) SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__helper1 SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__helper2.

Opaque SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__cond SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__Format.


Definition SSB_Configuration_r16__sfn0_Offset_r16__Format_Type := Eval cbn in seq_format_prod SSB_Configuration_r16__sfn0_Offset_r16__list.
Definition SSB_Configuration_r16__sfn0_Offset_r16__Format_list : SSB_Configuration_r16__sfn0_Offset_r16__Format_Type :=
  (SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16__Format, (SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16__Format, unit_format)).
Definition SSB_Configuration_r16__sfn0_Offset_r16__list__Format := (*Eval compute in *) seq_format SSB_Configuration_r16__sfn0_Offset_r16__list SSB_Configuration_r16__sfn0_Offset_r16__Format_list.
Definition SSB_Configuration_r16__sfn0_Offset_r16__F1 z :=
  (SSB_Configuration_r16__sfn0_Offset_r16__sfn_Offset_r16 z, (SSB_Configuration_r16__sfn0_Offset_r16__integerSubframeOffset_r16 z, tt)).
Definition SSB_Configuration_r16__sfn0_Offset_r16__F2 (y : seq_type SSB_Configuration_r16__sfn0_Offset_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SSB_Configuration_r16__sfn0_Offset_r16__Type i0 i1
  end.
Lemma SSB_Configuration_r16__sfn0_Offset_r16__F1F2_cond (z : SSB_Configuration_r16__sfn0_Offset_r16__Type)
  : SSB_Configuration_r16__sfn0_Offset_r16__cond z ->
  (seq_cond SSB_Configuration_r16__sfn0_Offset_r16__list (SSB_Configuration_r16__sfn0_Offset_r16__F1 z)).
intro H. unfold SSB_Configuration_r16__sfn0_Offset_r16__cond in H. simpl. auto. Qed.
Lemma SSB_Configuration_r16__sfn0_Offset_r16__F1F2_cond2 (z : SSB_Configuration_r16__sfn0_Offset_r16__Type)
 : SSB_Configuration_r16__sfn0_Offset_r16__F2 (SSB_Configuration_r16__sfn0_Offset_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_Configuration_r16__sfn0_Offset_r16__F2F1_cond (y : seq_type SSB_Configuration_r16__sfn0_Offset_r16__list)
  : seq_cond SSB_Configuration_r16__sfn0_Offset_r16__list y ->
 (SSB_Configuration_r16__sfn0_Offset_r16__cond (SSB_Configuration_r16__sfn0_Offset_r16__F2 y)) /\  SSB_Configuration_r16__sfn0_Offset_r16__F1 (SSB_Configuration_r16__sfn0_Offset_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_Configuration_r16__sfn0_Offset_r16__cond. simpl in *. auto.
 - simpl. unfold SSB_Configuration_r16__sfn0_Offset_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_Configuration_r16__sfn0_Offset_r16__Format : T_Format SSB_Configuration_r16__sfn0_Offset_r16__Type SSB_Configuration_r16__sfn0_Offset_r16__cond :=
        proj2_format  SSB_Configuration_r16__sfn0_Offset_r16__cond SSB_Configuration_r16__sfn0_Offset_r16__list__Format
    SSB_Configuration_r16__sfn0_Offset_r16__F1 SSB_Configuration_r16__sfn0_Offset_r16__F2 SSB_Configuration_r16__sfn0_Offset_r16__F1F2_cond  SSB_Configuration_r16__sfn0_Offset_r16__F1F2_cond2 SSB_Configuration_r16__sfn0_Offset_r16__F2F1_cond.
Opaque SSB_Configuration_r16__sfn0_Offset_r16__cond SSB_Configuration_r16__sfn0_Offset_r16__Format.

Definition SSB_Configuration_r16__sfn_SSB_Offset_r16__Format : T_Format Z SSB_Configuration_r16__sfn_SSB_Offset_r16__cond :=
 ranged_int_format (0) (15) SSB_Configuration_r16__sfn_SSB_Offset_r16__helper1 SSB_Configuration_r16__sfn_SSB_Offset_r16__helper2.

Opaque SSB_Configuration_r16__sfn_SSB_Offset_r16__cond SSB_Configuration_r16__sfn_SSB_Offset_r16__Format.

Definition SSB_Configuration_r16__ss_PBCH_BlockPower_r16__Format : T_Format Z SSB_Configuration_r16__ss_PBCH_BlockPower_r16__cond :=
 ranged_int_format (-60) (50) SSB_Configuration_r16__ss_PBCH_BlockPower_r16__helper1 SSB_Configuration_r16__ss_PBCH_BlockPower_r16__helper2.

Opaque SSB_Configuration_r16__ss_PBCH_BlockPower_r16__cond SSB_Configuration_r16__ss_PBCH_BlockPower_r16__Format.


Definition SSB_Configuration_r16__Format_Type := Eval cbn in seq_format_prod SSB_Configuration_r16__list.
Definition SSB_Configuration_r16__Format_list : SSB_Configuration_r16__Format_Type :=
  (ARFCN_ValueNR__Format, (SSB_Configuration_r16__halfFrameIndex_r16__Format, (SubcarrierSpacing__Format, (SSB_Configuration_r16__ssb_Periodicity_r16__Format, (SSB_Configuration_r16__sfn0_Offset_r16__Format, (SSB_Configuration_r16__sfn_SSB_Offset_r16__Format, (SSB_Configuration_r16__ss_PBCH_BlockPower_r16__Format, unit_format))))))).
Definition SSB_Configuration_r16__list__Format := (*Eval compute in *) seq_format SSB_Configuration_r16__list SSB_Configuration_r16__Format_list.
Definition SSB_Configuration_r16__F1 z :=
  (SSB_Configuration_r16__ssb_Freq_r16 z, (SSB_Configuration_r16__halfFrameIndex_r16 z, (SSB_Configuration_r16__ssbSubcarrierSpacing_r16 z, (SSB_Configuration_r16__ssb_Periodicity_r16 z, (SSB_Configuration_r16__sfn0_Offset_r16 z, (SSB_Configuration_r16__sfn_SSB_Offset_r16 z, (SSB_Configuration_r16__ss_PBCH_BlockPower_r16 z, tt))))))).
Definition SSB_Configuration_r16__F2 (y : seq_type SSB_Configuration_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__SSB_Configuration_r16__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma SSB_Configuration_r16__F1F2_cond (z : SSB_Configuration_r16__Type)
  : SSB_Configuration_r16__cond z ->
  (seq_cond SSB_Configuration_r16__list (SSB_Configuration_r16__F1 z)).
intro H. unfold SSB_Configuration_r16__cond in H. simpl. auto. Qed.
Lemma SSB_Configuration_r16__F1F2_cond2 (z : SSB_Configuration_r16__Type)
 : SSB_Configuration_r16__F2 (SSB_Configuration_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_Configuration_r16__F2F1_cond (y : seq_type SSB_Configuration_r16__list)
  : seq_cond SSB_Configuration_r16__list y ->
 (SSB_Configuration_r16__cond (SSB_Configuration_r16__F2 y)) /\  SSB_Configuration_r16__F1 (SSB_Configuration_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_Configuration_r16__cond. simpl in *. auto.
 - simpl. unfold SSB_Configuration_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_Configuration_r16__Format : T_Format SSB_Configuration_r16__Type SSB_Configuration_r16__cond :=
        proj2_format  SSB_Configuration_r16__cond SSB_Configuration_r16__list__Format
    SSB_Configuration_r16__F1 SSB_Configuration_r16__F2 SSB_Configuration_r16__F1F2_cond  SSB_Configuration_r16__F1F2_cond2 SSB_Configuration_r16__F2F1_cond.
Opaque SSB_Configuration_r16__cond SSB_Configuration_r16__Format.

