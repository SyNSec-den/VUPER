Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Type : Set :=
 | FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__supported
.
Definition FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__cond := (fun (_ : FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Type) => True).
Lemma FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__nat__helper.

Definition FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F1 t :=
  match t with
  | FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__supported => 0
  end.
Definition FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__supported
  | _ => FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__supported
  end.
Lemma FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F1F2 : forall x : FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Type, (FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F1 x <= 0) /\ FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F2 (FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F1 (FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Type : Set :=
 | FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__supported
.
Definition FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__cond := (fun (_ : FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Type) => True).
Lemma FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__nat__helper.

Definition FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F1 t :=
  match t with
  | FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__supported => 0
  end.
Definition FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__supported
  | _ => FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__supported
  end.
Lemma FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F1F2 : forall x : FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Type, (FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F1 x <= 0) /\ FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F2 (FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F1 (FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1540__pusch_SeparationWithGap__Type : Set :=
 | FeatureSetUplink_v1540__pusch_SeparationWithGap__supported
.
Definition FeatureSetUplink_v1540__pusch_SeparationWithGap__cond := (fun (_ : FeatureSetUplink_v1540__pusch_SeparationWithGap__Type) => True).
Lemma FeatureSetUplink_v1540__pusch_SeparationWithGap__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1540__pusch_SeparationWithGap__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink_v1540__pusch_SeparationWithGap__nat__helper.

Definition FeatureSetUplink_v1540__pusch_SeparationWithGap__F1 t :=
  match t with
  | FeatureSetUplink_v1540__pusch_SeparationWithGap__supported => 0
  end.
Definition FeatureSetUplink_v1540__pusch_SeparationWithGap__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1540__pusch_SeparationWithGap__supported
  | _ => FeatureSetUplink_v1540__pusch_SeparationWithGap__supported
  end.
Lemma FeatureSetUplink_v1540__pusch_SeparationWithGap__F1F2 : forall x : FeatureSetUplink_v1540__pusch_SeparationWithGap__Type, (FeatureSetUplink_v1540__pusch_SeparationWithGap__F1 x <= 0) /\ FeatureSetUplink_v1540__pusch_SeparationWithGap__F2 (FeatureSetUplink_v1540__pusch_SeparationWithGap__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1540__pusch_SeparationWithGap__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink_v1540__pusch_SeparationWithGap__F1 (FeatureSetUplink_v1540__pusch_SeparationWithGap__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ProcessingParameters.

Opaque ProcessingParameters__cond ProcessingParameters__Format.

Require Import NR.ProcessingParameters.

Opaque ProcessingParameters__cond ProcessingParameters__Format.

Require Import NR.ProcessingParameters.

Opaque ProcessingParameters__cond ProcessingParameters__Format.

Record FeatureSetUplink_v1540__pusch_ProcessingType2__Type : Set :=
  make__FeatureSetUplink_v1540__pusch_ProcessingType2__Type {
    FeatureSetUplink_v1540__pusch_ProcessingType2__scs_15kHz : option ProcessingParameters__Type ;
    FeatureSetUplink_v1540__pusch_ProcessingType2__scs_30kHz : option ProcessingParameters__Type ;
    FeatureSetUplink_v1540__pusch_ProcessingType2__scs_60kHz : option ProcessingParameters__Type ;
}.
Definition FeatureSetUplink_v1540__pusch_ProcessingType2__list := (
 Opt ProcessingParameters__Type ProcessingParameters__cond ::
 Opt ProcessingParameters__Type ProcessingParameters__cond ::
 Opt ProcessingParameters__Type ProcessingParameters__cond ::
 nil).
Definition FeatureSetUplink_v1540__pusch_ProcessingType2__cond z := 
  opt_cond ProcessingParameters__cond (FeatureSetUplink_v1540__pusch_ProcessingType2__scs_15kHz z) /\
  opt_cond ProcessingParameters__cond (FeatureSetUplink_v1540__pusch_ProcessingType2__scs_30kHz z) /\
  opt_cond ProcessingParameters__cond (FeatureSetUplink_v1540__pusch_ProcessingType2__scs_60kHz z) /\
  True.

Inductive FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Type : Set :=
 | FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__supported
.
Definition FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__cond := (fun (_ : FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Type) => True).
Lemma FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__nat__helper.

Definition FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F1 t :=
  match t with
  | FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__supported => 0
  end.
Definition FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__supported
  | _ => FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__supported
  end.
Lemma FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F1F2 : forall x : FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Type, (FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F1 x <= 0) /\ FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F2 (FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F1 (FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetUplink_v1540__Type : Set :=
  make__FeatureSetUplink_v1540__Type {
    FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS : option FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Type ;
    FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts : option FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Type ;
    FeatureSetUplink_v1540__pusch_SeparationWithGap : option FeatureSetUplink_v1540__pusch_SeparationWithGap__Type ;
    FeatureSetUplink_v1540__pusch_ProcessingType2 : option FeatureSetUplink_v1540__pusch_ProcessingType2__Type ;
    FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication : option FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Type ;
}.
Definition FeatureSetUplink_v1540__list := (
 Opt FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Type FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__cond ::
 Opt FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Type FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__cond ::
 Opt FeatureSetUplink_v1540__pusch_SeparationWithGap__Type FeatureSetUplink_v1540__pusch_SeparationWithGap__cond ::
 Opt FeatureSetUplink_v1540__pusch_ProcessingType2__Type FeatureSetUplink_v1540__pusch_ProcessingType2__cond ::
 Opt FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Type FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__cond ::
 nil).
Definition FeatureSetUplink_v1540__cond z := 
  opt_cond FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__cond (FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS z) /\
  opt_cond FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__cond (FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts z) /\
  opt_cond FeatureSetUplink_v1540__pusch_SeparationWithGap__cond (FeatureSetUplink_v1540__pusch_SeparationWithGap z) /\
  opt_cond FeatureSetUplink_v1540__pusch_ProcessingType2__cond (FeatureSetUplink_v1540__pusch_ProcessingType2 z) /\
  opt_cond FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__cond (FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication z) /\
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
Definition FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Format : T_Format FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__nat__Format FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F1 FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F2 FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F1F2 FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__F2F1.

Opaque FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__cond FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Format.

Definition FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Format : T_Format FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__nat__Format FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F1 FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F2 FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F1F2 FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__F2F1.

Opaque FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__cond FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Format.

Definition FeatureSetUplink_v1540__pusch_SeparationWithGap__Format : T_Format FeatureSetUplink_v1540__pusch_SeparationWithGap__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1540__pusch_SeparationWithGap__nat__Format FeatureSetUplink_v1540__pusch_SeparationWithGap__F1 FeatureSetUplink_v1540__pusch_SeparationWithGap__F2 FeatureSetUplink_v1540__pusch_SeparationWithGap__F1F2 FeatureSetUplink_v1540__pusch_SeparationWithGap__F2F1.

Opaque FeatureSetUplink_v1540__pusch_SeparationWithGap__cond FeatureSetUplink_v1540__pusch_SeparationWithGap__Format.


Definition FeatureSetUplink_v1540__pusch_ProcessingType2__Format_Type := Eval cbn in seq_format_prod FeatureSetUplink_v1540__pusch_ProcessingType2__list.
Definition FeatureSetUplink_v1540__pusch_ProcessingType2__Format_list : FeatureSetUplink_v1540__pusch_ProcessingType2__Format_Type :=
  (ProcessingParameters__Format, (ProcessingParameters__Format, (ProcessingParameters__Format, unit_format))).
Definition FeatureSetUplink_v1540__pusch_ProcessingType2__list__Format := (*Eval compute in *) seq_format FeatureSetUplink_v1540__pusch_ProcessingType2__list FeatureSetUplink_v1540__pusch_ProcessingType2__Format_list.
Definition FeatureSetUplink_v1540__pusch_ProcessingType2__F1 z :=
  (FeatureSetUplink_v1540__pusch_ProcessingType2__scs_15kHz z, (FeatureSetUplink_v1540__pusch_ProcessingType2__scs_30kHz z, (FeatureSetUplink_v1540__pusch_ProcessingType2__scs_60kHz z, tt))).
Definition FeatureSetUplink_v1540__pusch_ProcessingType2__F2 (y : seq_type FeatureSetUplink_v1540__pusch_ProcessingType2__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FeatureSetUplink_v1540__pusch_ProcessingType2__Type i0 i1 i2
  end.
Lemma FeatureSetUplink_v1540__pusch_ProcessingType2__F1F2_cond (z : FeatureSetUplink_v1540__pusch_ProcessingType2__Type)
  : FeatureSetUplink_v1540__pusch_ProcessingType2__cond z ->
  (seq_cond FeatureSetUplink_v1540__pusch_ProcessingType2__list (FeatureSetUplink_v1540__pusch_ProcessingType2__F1 z)).
intro H. unfold FeatureSetUplink_v1540__pusch_ProcessingType2__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplink_v1540__pusch_ProcessingType2__F1F2_cond2 (z : FeatureSetUplink_v1540__pusch_ProcessingType2__Type)
 : FeatureSetUplink_v1540__pusch_ProcessingType2__F2 (FeatureSetUplink_v1540__pusch_ProcessingType2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplink_v1540__pusch_ProcessingType2__F2F1_cond (y : seq_type FeatureSetUplink_v1540__pusch_ProcessingType2__list)
  : seq_cond FeatureSetUplink_v1540__pusch_ProcessingType2__list y ->
 (FeatureSetUplink_v1540__pusch_ProcessingType2__cond (FeatureSetUplink_v1540__pusch_ProcessingType2__F2 y)) /\  FeatureSetUplink_v1540__pusch_ProcessingType2__F1 (FeatureSetUplink_v1540__pusch_ProcessingType2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplink_v1540__pusch_ProcessingType2__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplink_v1540__pusch_ProcessingType2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplink_v1540__pusch_ProcessingType2__Format : T_Format FeatureSetUplink_v1540__pusch_ProcessingType2__Type FeatureSetUplink_v1540__pusch_ProcessingType2__cond :=
        proj2_format  FeatureSetUplink_v1540__pusch_ProcessingType2__cond FeatureSetUplink_v1540__pusch_ProcessingType2__list__Format
    FeatureSetUplink_v1540__pusch_ProcessingType2__F1 FeatureSetUplink_v1540__pusch_ProcessingType2__F2 FeatureSetUplink_v1540__pusch_ProcessingType2__F1F2_cond  FeatureSetUplink_v1540__pusch_ProcessingType2__F1F2_cond2 FeatureSetUplink_v1540__pusch_ProcessingType2__F2F1_cond.
Opaque FeatureSetUplink_v1540__pusch_ProcessingType2__cond FeatureSetUplink_v1540__pusch_ProcessingType2__Format.

Definition FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Format : T_Format FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__nat__Format FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F1 FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F2 FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F1F2 FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__F2F1.

Opaque FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__cond FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Format.


Definition FeatureSetUplink_v1540__Format_Type := Eval cbn in seq_format_prod FeatureSetUplink_v1540__list.
Definition FeatureSetUplink_v1540__Format_list : FeatureSetUplink_v1540__Format_Type :=
  (FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS__Format, (FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts__Format, (FeatureSetUplink_v1540__pusch_SeparationWithGap__Format, (FeatureSetUplink_v1540__pusch_ProcessingType2__Format, (FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication__Format, unit_format))))).
Definition FeatureSetUplink_v1540__list__Format := (*Eval compute in *) seq_format FeatureSetUplink_v1540__list FeatureSetUplink_v1540__Format_list.
Definition FeatureSetUplink_v1540__F1 z :=
  (FeatureSetUplink_v1540__zeroSlotOffsetAperiodicSRS z, (FeatureSetUplink_v1540__pa_PhaseDiscontinuityImpacts z, (FeatureSetUplink_v1540__pusch_SeparationWithGap z, (FeatureSetUplink_v1540__pusch_ProcessingType2 z, (FeatureSetUplink_v1540__ul_MCS_TableAlt_DynamicIndication z, tt))))).
Definition FeatureSetUplink_v1540__F2 (y : seq_type FeatureSetUplink_v1540__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__FeatureSetUplink_v1540__Type i0 i1 i2 i3 i4
  end.
Lemma FeatureSetUplink_v1540__F1F2_cond (z : FeatureSetUplink_v1540__Type)
  : FeatureSetUplink_v1540__cond z ->
  (seq_cond FeatureSetUplink_v1540__list (FeatureSetUplink_v1540__F1 z)).
intro H. unfold FeatureSetUplink_v1540__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplink_v1540__F1F2_cond2 (z : FeatureSetUplink_v1540__Type)
 : FeatureSetUplink_v1540__F2 (FeatureSetUplink_v1540__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplink_v1540__F2F1_cond (y : seq_type FeatureSetUplink_v1540__list)
  : seq_cond FeatureSetUplink_v1540__list y ->
 (FeatureSetUplink_v1540__cond (FeatureSetUplink_v1540__F2 y)) /\  FeatureSetUplink_v1540__F1 (FeatureSetUplink_v1540__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplink_v1540__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplink_v1540__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplink_v1540__Format : T_Format FeatureSetUplink_v1540__Type FeatureSetUplink_v1540__cond :=
        proj2_format  FeatureSetUplink_v1540__cond FeatureSetUplink_v1540__list__Format
    FeatureSetUplink_v1540__F1 FeatureSetUplink_v1540__F2 FeatureSetUplink_v1540__F1F2_cond  FeatureSetUplink_v1540__F1F2_cond2 FeatureSetUplink_v1540__F2F1_cond.
Opaque FeatureSetUplink_v1540__cond FeatureSetUplink_v1540__Format.

