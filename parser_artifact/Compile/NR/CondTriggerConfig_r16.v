Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasTriggerQuantityOffset.

Opaque MeasTriggerQuantityOffset__cond MeasTriggerQuantityOffset__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record CondTriggerConfig_r16__condEventId__root__condEventA3__Type : Set :=
  make__CondTriggerConfig_r16__condEventId__root__condEventA3__Type {
    CondTriggerConfig_r16__condEventId__root__condEventA3__a3_Offset : MeasTriggerQuantityOffset__Type ;
    CondTriggerConfig_r16__condEventId__root__condEventA3__hysteresis : Hysteresis__Type ;
    CondTriggerConfig_r16__condEventId__root__condEventA3__timeToTrigger : TimeToTrigger__Type ;
}.
Definition CondTriggerConfig_r16__condEventId__root__condEventA3__list := (
 Nor MeasTriggerQuantityOffset__Type MeasTriggerQuantityOffset__cond ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition CondTriggerConfig_r16__condEventId__root__condEventA3__cond z := 
  MeasTriggerQuantityOffset__cond (CondTriggerConfig_r16__condEventId__root__condEventA3__a3_Offset z) /\
  Hysteresis__cond (CondTriggerConfig_r16__condEventId__root__condEventA3__hysteresis z) /\
  TimeToTrigger__cond (CondTriggerConfig_r16__condEventId__root__condEventA3__timeToTrigger z) /\
  True.

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record CondTriggerConfig_r16__condEventId__root__condEventA5__Type : Set :=
  make__CondTriggerConfig_r16__condEventId__root__condEventA5__Type {
    CondTriggerConfig_r16__condEventId__root__condEventA5__a5_Threshold1 : MeasTriggerQuantity__Type ;
    CondTriggerConfig_r16__condEventId__root__condEventA5__a5_Threshold2 : MeasTriggerQuantity__Type ;
    CondTriggerConfig_r16__condEventId__root__condEventA5__hysteresis : Hysteresis__Type ;
    CondTriggerConfig_r16__condEventId__root__condEventA5__timeToTrigger : TimeToTrigger__Type ;
}.
Definition CondTriggerConfig_r16__condEventId__root__condEventA5__list := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition CondTriggerConfig_r16__condEventId__root__condEventA5__cond z := 
  MeasTriggerQuantity__cond (CondTriggerConfig_r16__condEventId__root__condEventA5__a5_Threshold1 z) /\
  MeasTriggerQuantity__cond (CondTriggerConfig_r16__condEventId__root__condEventA5__a5_Threshold2 z) /\
  Hysteresis__cond (CondTriggerConfig_r16__condEventId__root__condEventA5__hysteresis z) /\
  TimeToTrigger__cond (CondTriggerConfig_r16__condEventId__root__condEventA5__timeToTrigger z) /\
  True.


Inductive CondTriggerConfig_r16__condEventId__root__Type : Set :=
  | CondTriggerConfig_r16__condEventId__root__condEventA3 : CondTriggerConfig_r16__condEventId__root__condEventA3__Type -> CondTriggerConfig_r16__condEventId__root__Type
  | CondTriggerConfig_r16__condEventId__root__condEventA5 : CondTriggerConfig_r16__condEventId__root__condEventA5__Type -> CondTriggerConfig_r16__condEventId__root__Type
.
Definition CondTriggerConfig_r16__condEventId__root__list : list typ := (
typ_cons CondTriggerConfig_r16__condEventId__root__condEventA3__Type CondTriggerConfig_r16__condEventId__root__condEventA3__cond ::
typ_cons CondTriggerConfig_r16__condEventId__root__condEventA5__Type CondTriggerConfig_r16__condEventId__root__condEventA5__cond ::
 nil).
Definition CondTriggerConfig_r16__condEventId__root__cond (c : CondTriggerConfig_r16__condEventId__root__Type) := 
  match c with
  | CondTriggerConfig_r16__condEventId__root__condEventA3 t => CondTriggerConfig_r16__condEventId__root__condEventA3__cond t 
  | CondTriggerConfig_r16__condEventId__root__condEventA5 t => CondTriggerConfig_r16__condEventId__root__condEventA5__cond t 
  end.

Lemma CondTriggerConfig_r16__condEventId__root__len_helper1 : to_bit_sz (length CondTriggerConfig_r16__condEventId__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CondTriggerConfig_r16__condEventId__root__len_helper2 : 2 <= length2 CondTriggerConfig_r16__condEventId__root__list.
 simpl. lia. Qed.
Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type : Set :=
  make__CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type {
    CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__a4_Threshold_r17 : MeasTriggerQuantity__Type ;
    CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__hysteresis_r17 : Hysteresis__Type ;
    CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__timeToTrigger_r17 : TimeToTrigger__Type ;
}.
Definition CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond z := 
  MeasTriggerQuantity__cond (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__a4_Threshold_r17 z) /\
  Hysteresis__cond (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__hysteresis_r17 z) /\
  TimeToTrigger__cond (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__timeToTrigger_r17 z) /\
  True.

Lemma CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__helper1 : (0 <= 65525)%Z.  lia. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__helper2 : to_bit_sz (Z.to_nat (65525 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65525 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__Type := Z.
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__cond := (fun z => (0 <= z <= 65525)%Z).
Lemma CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__helper1 : (0 <= 65525)%Z.  lia. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__helper2 : to_bit_sz (Z.to_nat (65525 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65525 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__Type := Z.
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__cond := (fun z => (0 <= z <= 65525)%Z).
Require Import NR.ReferenceLocation_r17.

Opaque ReferenceLocation_r17__cond ReferenceLocation_r17__Format.

Require Import NR.ReferenceLocation_r17.

Opaque ReferenceLocation_r17__cond ReferenceLocation_r17__Format.

Require Import NR.HysteresisLocation_r17.

Opaque HysteresisLocation_r17__cond HysteresisLocation_r17__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type : Set :=
  make__CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type {
    CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17 : Z ;
    CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17 : Z ;
    CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__referenceLocation1_r17 : ReferenceLocation_r17__Type ;
    CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__referenceLocation2_r17 : ReferenceLocation_r17__Type ;
    CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__hysteresisLocation_r17 : HysteresisLocation_r17__Type ;
    CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__timeToTrigger_r17 : TimeToTrigger__Type ;
}.
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list := (
 Nor Z CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__cond ::
 Nor Z CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__cond ::
 Nor ReferenceLocation_r17__Type ReferenceLocation_r17__cond ::
 Nor ReferenceLocation_r17__Type ReferenceLocation_r17__cond ::
 Nor HysteresisLocation_r17__Type HysteresisLocation_r17__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond z := 
  CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17 z) /\
  CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17 z) /\
  ReferenceLocation_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__referenceLocation1_r17 z) /\
  ReferenceLocation_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__referenceLocation2_r17 z) /\
  HysteresisLocation_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__hysteresisLocation_r17 z) /\
  TimeToTrigger__cond (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__timeToTrigger_r17 z) /\
  True.

Lemma CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__helper1 : (0 <= 549755813887)%Z.  lia. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__helper2 : to_bit_sz (Z.to_nat (549755813887 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (549755813887 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__Type := Z.
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__cond := (fun z => (0 <= z <= 549755813887)%Z).
Lemma CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__helper1 : (1 <= 6000)%Z.  lia. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__helper2 : to_bit_sz (Z.to_nat (6000 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6000 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__Type := Z.
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__cond := (fun z => (1 <= z <= 6000)%Z).
Record CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type : Set :=
  make__CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type {
    CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17 : Z ;
    CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17 : Z ;
}.
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list := (
 Nor Z CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__cond ::
 Nor Z CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__cond ::
 nil).
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond z := 
  CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17 z) /\
  CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17 z) /\
  True.


Inductive CondTriggerConfig_r16__condEventId__ext__Type : Set :=
  | CondTriggerConfig_r16__condEventId__ext__condEventA4_r17 : CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type -> CondTriggerConfig_r16__condEventId__ext__Type
  | CondTriggerConfig_r16__condEventId__ext__condEventD1_r17 : CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type -> CondTriggerConfig_r16__condEventId__ext__Type
  | CondTriggerConfig_r16__condEventId__ext__condEventT1_r17 : CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type -> CondTriggerConfig_r16__condEventId__ext__Type
.
Definition CondTriggerConfig_r16__condEventId__ext__list : list typ := (
typ_cons CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond ::
typ_cons CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond ::
typ_cons CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond ::
 nil).
Definition CondTriggerConfig_r16__condEventId__ext__cond (c : CondTriggerConfig_r16__condEventId__ext__Type) := 
  match c with
  | CondTriggerConfig_r16__condEventId__ext__condEventA4_r17 t => CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond t 
  | CondTriggerConfig_r16__condEventId__ext__condEventD1_r17 t => CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond t 
  | CondTriggerConfig_r16__condEventId__ext__condEventT1_r17 t => CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond t 
  end.

Lemma CondTriggerConfig_r16__condEventId__ext__len_helper1 : to_bit_sz (length CondTriggerConfig_r16__condEventId__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition CondTriggerConfig_r16__condEventId__Type : Set := CondTriggerConfig_r16__condEventId__root__Type + CondTriggerConfig_r16__condEventId__ext__Type.
Definition CondTriggerConfig_r16__condEventId__cond :=
  sum_cond CondTriggerConfig_r16__condEventId__root__cond CondTriggerConfig_r16__condEventId__ext__cond.
Require Import NR.NR_RS_Type.

Opaque NR_RS_Type__cond NR_RS_Type__Format.

Record CondTriggerConfig_r16__Type : Set :=
  make__CondTriggerConfig_r16__Type {
    CondTriggerConfig_r16__condEventId : CondTriggerConfig_r16__condEventId__Type ;
    CondTriggerConfig_r16__rsType_r16 : NR_RS_Type__Type ;
}.
Definition CondTriggerConfig_r16__root_list : list seq_elem := (
 Nor CondTriggerConfig_r16__condEventId__Type CondTriggerConfig_r16__condEventId__cond ::
 Nor NR_RS_Type__Type NR_RS_Type__cond ::
 nil).
Definition CondTriggerConfig_r16__ext_list : list typ := (
  nil).
Definition CondTriggerConfig_r16__cond (z : CondTriggerConfig_r16__Type) := 
(  CondTriggerConfig_r16__condEventId__cond (CondTriggerConfig_r16__condEventId z) /\
  NR_RS_Type__cond (CondTriggerConfig_r16__rsType_r16 z) /\
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

Definition CondTriggerConfig_r16__condEventId__root__condEventA3__Format_Type := Eval cbn in seq_format_prod CondTriggerConfig_r16__condEventId__root__condEventA3__list.
Definition CondTriggerConfig_r16__condEventId__root__condEventA3__Format_list : CondTriggerConfig_r16__condEventId__root__condEventA3__Format_Type :=
  (MeasTriggerQuantityOffset__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format))).
Definition CondTriggerConfig_r16__condEventId__root__condEventA3__list__Format := (*Eval compute in *) seq_format CondTriggerConfig_r16__condEventId__root__condEventA3__list CondTriggerConfig_r16__condEventId__root__condEventA3__Format_list.
Definition CondTriggerConfig_r16__condEventId__root__condEventA3__F1 z :=
  (CondTriggerConfig_r16__condEventId__root__condEventA3__a3_Offset z, (CondTriggerConfig_r16__condEventId__root__condEventA3__hysteresis z, (CondTriggerConfig_r16__condEventId__root__condEventA3__timeToTrigger z, tt))).
Definition CondTriggerConfig_r16__condEventId__root__condEventA3__F2 (y : seq_type CondTriggerConfig_r16__condEventId__root__condEventA3__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CondTriggerConfig_r16__condEventId__root__condEventA3__Type i0 i1 i2
  end.
Lemma CondTriggerConfig_r16__condEventId__root__condEventA3__F1F2_cond (z : CondTriggerConfig_r16__condEventId__root__condEventA3__Type)
  : CondTriggerConfig_r16__condEventId__root__condEventA3__cond z ->
  (seq_cond CondTriggerConfig_r16__condEventId__root__condEventA3__list (CondTriggerConfig_r16__condEventId__root__condEventA3__F1 z)).
intro H. unfold CondTriggerConfig_r16__condEventId__root__condEventA3__cond in H. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__root__condEventA3__F1F2_cond2 (z : CondTriggerConfig_r16__condEventId__root__condEventA3__Type)
 : CondTriggerConfig_r16__condEventId__root__condEventA3__F2 (CondTriggerConfig_r16__condEventId__root__condEventA3__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__root__condEventA3__F2F1_cond (y : seq_type CondTriggerConfig_r16__condEventId__root__condEventA3__list)
  : seq_cond CondTriggerConfig_r16__condEventId__root__condEventA3__list y ->
 (CondTriggerConfig_r16__condEventId__root__condEventA3__cond (CondTriggerConfig_r16__condEventId__root__condEventA3__F2 y)) /\  CondTriggerConfig_r16__condEventId__root__condEventA3__F1 (CondTriggerConfig_r16__condEventId__root__condEventA3__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CondTriggerConfig_r16__condEventId__root__condEventA3__cond. simpl in *. auto.
 - simpl. unfold CondTriggerConfig_r16__condEventId__root__condEventA3__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CondTriggerConfig_r16__condEventId__root__condEventA3__Format : T_Format CondTriggerConfig_r16__condEventId__root__condEventA3__Type CondTriggerConfig_r16__condEventId__root__condEventA3__cond :=
        proj2_format  CondTriggerConfig_r16__condEventId__root__condEventA3__cond CondTriggerConfig_r16__condEventId__root__condEventA3__list__Format
    CondTriggerConfig_r16__condEventId__root__condEventA3__F1 CondTriggerConfig_r16__condEventId__root__condEventA3__F2 CondTriggerConfig_r16__condEventId__root__condEventA3__F1F2_cond  CondTriggerConfig_r16__condEventId__root__condEventA3__F1F2_cond2 CondTriggerConfig_r16__condEventId__root__condEventA3__F2F1_cond.
Opaque CondTriggerConfig_r16__condEventId__root__condEventA3__cond CondTriggerConfig_r16__condEventId__root__condEventA3__Format.


Definition CondTriggerConfig_r16__condEventId__root__condEventA5__Format_Type := Eval cbn in seq_format_prod CondTriggerConfig_r16__condEventId__root__condEventA5__list.
Definition CondTriggerConfig_r16__condEventId__root__condEventA5__Format_list : CondTriggerConfig_r16__condEventId__root__condEventA5__Format_Type :=
  (MeasTriggerQuantity__Format, (MeasTriggerQuantity__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).
Definition CondTriggerConfig_r16__condEventId__root__condEventA5__list__Format := (*Eval compute in *) seq_format CondTriggerConfig_r16__condEventId__root__condEventA5__list CondTriggerConfig_r16__condEventId__root__condEventA5__Format_list.
Definition CondTriggerConfig_r16__condEventId__root__condEventA5__F1 z :=
  (CondTriggerConfig_r16__condEventId__root__condEventA5__a5_Threshold1 z, (CondTriggerConfig_r16__condEventId__root__condEventA5__a5_Threshold2 z, (CondTriggerConfig_r16__condEventId__root__condEventA5__hysteresis z, (CondTriggerConfig_r16__condEventId__root__condEventA5__timeToTrigger z, tt)))).
Definition CondTriggerConfig_r16__condEventId__root__condEventA5__F2 (y : seq_type CondTriggerConfig_r16__condEventId__root__condEventA5__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CondTriggerConfig_r16__condEventId__root__condEventA5__Type i0 i1 i2 i3
  end.
Lemma CondTriggerConfig_r16__condEventId__root__condEventA5__F1F2_cond (z : CondTriggerConfig_r16__condEventId__root__condEventA5__Type)
  : CondTriggerConfig_r16__condEventId__root__condEventA5__cond z ->
  (seq_cond CondTriggerConfig_r16__condEventId__root__condEventA5__list (CondTriggerConfig_r16__condEventId__root__condEventA5__F1 z)).
intro H. unfold CondTriggerConfig_r16__condEventId__root__condEventA5__cond in H. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__root__condEventA5__F1F2_cond2 (z : CondTriggerConfig_r16__condEventId__root__condEventA5__Type)
 : CondTriggerConfig_r16__condEventId__root__condEventA5__F2 (CondTriggerConfig_r16__condEventId__root__condEventA5__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__root__condEventA5__F2F1_cond (y : seq_type CondTriggerConfig_r16__condEventId__root__condEventA5__list)
  : seq_cond CondTriggerConfig_r16__condEventId__root__condEventA5__list y ->
 (CondTriggerConfig_r16__condEventId__root__condEventA5__cond (CondTriggerConfig_r16__condEventId__root__condEventA5__F2 y)) /\  CondTriggerConfig_r16__condEventId__root__condEventA5__F1 (CondTriggerConfig_r16__condEventId__root__condEventA5__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CondTriggerConfig_r16__condEventId__root__condEventA5__cond. simpl in *. auto.
 - simpl. unfold CondTriggerConfig_r16__condEventId__root__condEventA5__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CondTriggerConfig_r16__condEventId__root__condEventA5__Format : T_Format CondTriggerConfig_r16__condEventId__root__condEventA5__Type CondTriggerConfig_r16__condEventId__root__condEventA5__cond :=
        proj2_format  CondTriggerConfig_r16__condEventId__root__condEventA5__cond CondTriggerConfig_r16__condEventId__root__condEventA5__list__Format
    CondTriggerConfig_r16__condEventId__root__condEventA5__F1 CondTriggerConfig_r16__condEventId__root__condEventA5__F2 CondTriggerConfig_r16__condEventId__root__condEventA5__F1F2_cond  CondTriggerConfig_r16__condEventId__root__condEventA5__F1F2_cond2 CondTriggerConfig_r16__condEventId__root__condEventA5__F2F1_cond.
Opaque CondTriggerConfig_r16__condEventId__root__condEventA5__cond CondTriggerConfig_r16__condEventId__root__condEventA5__Format.


Definition CondTriggerConfig_r16__condEventId__root__Format_Type := Eval cbn in get_formats CondTriggerConfig_r16__condEventId__root__list.
Definition CondTriggerConfig_r16__condEventId__root__Format_list : CondTriggerConfig_r16__condEventId__root__Format_Type :=
  (CondTriggerConfig_r16__condEventId__root__condEventA3__Format, (CondTriggerConfig_r16__condEventId__root__condEventA5__Format, unit__Format)).
Definition CondTriggerConfig_r16__condEventId__root__list__Format := Eval compute in choice_format CondTriggerConfig_r16__condEventId__root__list CondTriggerConfig_r16__condEventId__root__len_helper1 CondTriggerConfig_r16__condEventId__root__len_helper2  CondTriggerConfig_r16__condEventId__root__Format_list.
Definition CondTriggerConfig_r16__condEventId__root__F1 (z : CondTriggerConfig_r16__condEventId__root__Type) : (choice CondTriggerConfig_r16__condEventId__root__list) :=
  match z with
   | CondTriggerConfig_r16__condEventId__root__condEventA3 t => existT _ 0 t
  | CondTriggerConfig_r16__condEventId__root__condEventA5 t => existT _ 1 t
  end.
Definition CondTriggerConfig_r16__condEventId__root__g := (fun n => typ_set (get_nth_typ CondTriggerConfig_r16__condEventId__root__list n)).
Definition CondTriggerConfig_r16__condEventId__root__F2 (y : choice CondTriggerConfig_r16__condEventId__root__list) : CondTriggerConfig_r16__condEventId__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CondTriggerConfig_r16__condEventId__root__g n -> CondTriggerConfig_r16__condEventId__root__Type) with
    | 0 => fun (t : CondTriggerConfig_r16__condEventId__root__condEventA3__Type) => CondTriggerConfig_r16__condEventId__root__condEventA3 t 
    | 1 => fun (t : CondTriggerConfig_r16__condEventId__root__condEventA5__Type) => CondTriggerConfig_r16__condEventId__root__condEventA5 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CondTriggerConfig_r16__condEventId__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CondTriggerConfig_r16__condEventId__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CondTriggerConfig_r16__condEventId__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CondTriggerConfig_r16__condEventId__root__Type with end) n0
           end t0).

Lemma CondTriggerConfig_r16__condEventId__root__helper2 :  forall (y : CondTriggerConfig_r16__condEventId__root__Type), CondTriggerConfig_r16__condEventId__root__cond y -> choice_cond CondTriggerConfig_r16__condEventId__root__list (CondTriggerConfig_r16__condEventId__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CondTriggerConfig_r16__condEventId__root__helper3 :  forall (y : CondTriggerConfig_r16__condEventId__root__Type), CondTriggerConfig_r16__condEventId__root__F2 (CondTriggerConfig_r16__condEventId__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CondTriggerConfig_r16__condEventId__root__helper4 : (forall b : choice CondTriggerConfig_r16__condEventId__root__list, choice_cond CondTriggerConfig_r16__condEventId__root__list b -> CondTriggerConfig_r16__condEventId__root__cond (CondTriggerConfig_r16__condEventId__root__F2 b) /\ CondTriggerConfig_r16__condEventId__root__F1 (CondTriggerConfig_r16__condEventId__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CondTriggerConfig_r16__condEventId__root__F1 CondTriggerConfig_r16__condEventId__root__F2.
Definition CondTriggerConfig_r16__condEventId__root__Format : T_Format CondTriggerConfig_r16__condEventId__root__Type CondTriggerConfig_r16__condEventId__root__cond :=
  (* Eval compute in *) proj2_format CondTriggerConfig_r16__condEventId__root__cond CondTriggerConfig_r16__condEventId__root__list__Format CondTriggerConfig_r16__condEventId__root__F1 CondTriggerConfig_r16__condEventId__root__F2 CondTriggerConfig_r16__condEventId__root__helper2 CondTriggerConfig_r16__condEventId__root__helper3 CondTriggerConfig_r16__condEventId__root__helper4.
Opaque CondTriggerConfig_r16__condEventId__root__cond CondTriggerConfig_r16__condEventId__root__Format.


Definition CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format_Type := Eval cbn in seq_format_prod CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list.
Definition CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format_list : CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format_Type :=
  (MeasTriggerQuantity__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format))).
Definition CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list__Format := (*Eval compute in *) seq_format CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format_list.
Definition CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1 z :=
  (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__a4_Threshold_r17 z, (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__hysteresis_r17 z, (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__timeToTrigger_r17 z, tt))).
Definition CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F2 (y : seq_type CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type i0 i1 i2
  end.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1F2_cond (z : CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type)
  : CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond z ->
  (seq_cond CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1 z)).
intro H. unfold CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond in H. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1F2_cond2 (z : CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type)
 : CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F2 (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F2F1_cond (y : seq_type CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list)
  : seq_cond CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list y ->
 (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F2 y)) /\  CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1 (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond. simpl in *. auto.
 - simpl. unfold CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format : T_Format CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond :=
        proj2_format  CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__list__Format
    CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1 CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F2 CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1F2_cond  CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F1F2_cond2 CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__F2F1_cond.
Opaque CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format.

Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__Format : T_Format Z CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__cond :=
 ranged_int_format (0) (65525) CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__helper1 CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__helper2.

Opaque CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__Format.

Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__Format : T_Format Z CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__cond :=
 ranged_int_format (0) (65525) CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__helper1 CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__helper2.

Opaque CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__Format.


Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format_Type := Eval cbn in seq_format_prod CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list.
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format_list : CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format_Type :=
  (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17__Format, (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17__Format, (ReferenceLocation_r17__Format, (ReferenceLocation_r17__Format, (HysteresisLocation_r17__Format, (TimeToTrigger__Format, unit_format)))))).
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list__Format := (*Eval compute in *) seq_format CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format_list.
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1 z :=
  (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference1_r17 z, (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__distanceThreshFromReference2_r17 z, (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__referenceLocation1_r17 z, (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__referenceLocation2_r17 z, (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__hysteresisLocation_r17 z, (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__timeToTrigger_r17 z, tt)))))).
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F2 (y : seq_type CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type i0 i1 i2 i3 i4 i5
  end.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1F2_cond (z : CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type)
  : CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond z ->
  (seq_cond CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1 z)).
intro H. unfold CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond in H. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1F2_cond2 (z : CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type)
 : CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F2 (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F2F1_cond (y : seq_type CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list)
  : seq_cond CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list y ->
 (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F2 y)) /\  CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1 (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond. simpl in *. auto.
 - simpl. unfold CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format : T_Format CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond :=
        proj2_format  CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__list__Format
    CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1 CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F2 CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1F2_cond  CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F1F2_cond2 CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__F2F1_cond.
Opaque CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format.

Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__Format : T_Format Z CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__cond :=
 ranged_int_format (0) (549755813887) CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__helper1 CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__helper2.

Opaque CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__Format.

Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__Format : T_Format Z CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__cond :=
 ranged_int_format (1) (6000) CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__helper1 CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__helper2.

Opaque CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__Format.


Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format_Type := Eval cbn in seq_format_prod CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list.
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format_list : CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format_Type :=
  (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17__Format, (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17__Format, unit_format)).
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list__Format := (*Eval compute in *) seq_format CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format_list.
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1 z :=
  (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__t1_Threshold_r17 z, (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__duration_r17 z, tt)).
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F2 (y : seq_type CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type i0 i1
  end.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1F2_cond (z : CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type)
  : CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond z ->
  (seq_cond CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1 z)).
intro H. unfold CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond in H. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1F2_cond2 (z : CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type)
 : CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F2 (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F2F1_cond (y : seq_type CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list)
  : seq_cond CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list y ->
 (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F2 y)) /\  CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1 (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond. simpl in *. auto.
 - simpl. unfold CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format : T_Format CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond :=
        proj2_format  CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__list__Format
    CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1 CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F2 CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1F2_cond  CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F1F2_cond2 CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__F2F1_cond.
Opaque CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__cond CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format.


Definition CondTriggerConfig_r16__condEventId__ext__Format_Type := Eval cbn in get_formats CondTriggerConfig_r16__condEventId__ext__list.
Definition CondTriggerConfig_r16__condEventId__ext__Format_list : CondTriggerConfig_r16__condEventId__ext__Format_Type :=
  (CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Format, (CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Format, (CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Format, unit__Format))).
Definition CondTriggerConfig_r16__condEventId__ext__list__Format := Eval compute in choice_ext_format CondTriggerConfig_r16__condEventId__ext__list CondTriggerConfig_r16__condEventId__ext__Format_list.
Definition CondTriggerConfig_r16__condEventId__ext__F1 (z : CondTriggerConfig_r16__condEventId__ext__Type) : (choice CondTriggerConfig_r16__condEventId__ext__list) :=
  match z with
   | CondTriggerConfig_r16__condEventId__ext__condEventA4_r17 t => existT _ 0 t
  | CondTriggerConfig_r16__condEventId__ext__condEventD1_r17 t => existT _ 1 t
  | CondTriggerConfig_r16__condEventId__ext__condEventT1_r17 t => existT _ 2 t
  end.
Definition CondTriggerConfig_r16__condEventId__ext__g := (fun n => typ_set (get_nth_typ CondTriggerConfig_r16__condEventId__ext__list n)).
Definition CondTriggerConfig_r16__condEventId__ext__F2 (y : choice CondTriggerConfig_r16__condEventId__ext__list) : CondTriggerConfig_r16__condEventId__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CondTriggerConfig_r16__condEventId__ext__g n -> CondTriggerConfig_r16__condEventId__ext__Type) with
    | 0 => fun (t : CondTriggerConfig_r16__condEventId__ext__condEventA4_r17__Type) => CondTriggerConfig_r16__condEventId__ext__condEventA4_r17 t 
    | 1 => fun (t : CondTriggerConfig_r16__condEventId__ext__condEventD1_r17__Type) => CondTriggerConfig_r16__condEventId__ext__condEventD1_r17 t 
    | 2 => fun (t : CondTriggerConfig_r16__condEventId__ext__condEventT1_r17__Type) => CondTriggerConfig_r16__condEventId__ext__condEventT1_r17 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : CondTriggerConfig_r16__condEventId__ext__g (S (S (S x')))) =>let t' :=
                       eq_rect (get_nth_typ CondTriggerConfig_r16__condEventId__ext__list (S (S (S x'))))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len CondTriggerConfig_r16__condEventId__ext__list (S (S (S x')))
                       (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return CondTriggerConfig_r16__condEventId__ext__Type with end) n0
                       end t0).

Lemma CondTriggerConfig_r16__condEventId__ext__helper2 :  forall (y : CondTriggerConfig_r16__condEventId__ext__Type), CondTriggerConfig_r16__condEventId__ext__cond y -> choice_cond CondTriggerConfig_r16__condEventId__ext__list (CondTriggerConfig_r16__condEventId__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CondTriggerConfig_r16__condEventId__ext__helper3 :  forall (y : CondTriggerConfig_r16__condEventId__ext__Type), CondTriggerConfig_r16__condEventId__ext__F2 (CondTriggerConfig_r16__condEventId__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CondTriggerConfig_r16__condEventId__ext__helper4 : (forall b : choice CondTriggerConfig_r16__condEventId__ext__list, choice_cond CondTriggerConfig_r16__condEventId__ext__list b -> CondTriggerConfig_r16__condEventId__ext__cond (CondTriggerConfig_r16__condEventId__ext__F2 b) /\ CondTriggerConfig_r16__condEventId__ext__F1 (CondTriggerConfig_r16__condEventId__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CondTriggerConfig_r16__condEventId__ext__F1 CondTriggerConfig_r16__condEventId__ext__F2.
Definition CondTriggerConfig_r16__condEventId__ext__Format : T_Format CondTriggerConfig_r16__condEventId__ext__Type CondTriggerConfig_r16__condEventId__ext__cond :=
          proj2_format CondTriggerConfig_r16__condEventId__ext__cond CondTriggerConfig_r16__condEventId__ext__list__Format CondTriggerConfig_r16__condEventId__ext__F1 CondTriggerConfig_r16__condEventId__ext__F2 CondTriggerConfig_r16__condEventId__ext__helper2 CondTriggerConfig_r16__condEventId__ext__helper3 CondTriggerConfig_r16__condEventId__ext__helper4.
Opaque CondTriggerConfig_r16__condEventId__ext__cond CondTriggerConfig_r16__condEventId__ext__Format.

Definition CondTriggerConfig_r16__condEventId__Format : T_Format CondTriggerConfig_r16__condEventId__Type CondTriggerConfig_r16__condEventId__cond := sum_format CondTriggerConfig_r16__condEventId__root__Format CondTriggerConfig_r16__condEventId__ext__Format.
Opaque CondTriggerConfig_r16__condEventId__cond CondTriggerConfig_r16__condEventId__Format.


Definition CondTriggerConfig_r16__root_Format_Type := Eval cbn in seq_format_prod CondTriggerConfig_r16__root_list.
Definition CondTriggerConfig_r16__root_Format_list : CondTriggerConfig_r16__root_Format_Type :=
  (CondTriggerConfig_r16__condEventId__Format, (NR_RS_Type__Format, unit_format)).

Definition CondTriggerConfig_r16__ext_Format_Type := Eval cbn in get_formats CondTriggerConfig_r16__ext_list.
Definition CondTriggerConfig_r16__ext_Format_list : CondTriggerConfig_r16__ext_Format_Type :=
  unit__Format.

Definition CondTriggerConfig_r16__list_type : Set := (seq_type CondTriggerConfig_r16__root_list) * (seq_ext_type CondTriggerConfig_r16__ext_list).
Definition CondTriggerConfig_r16__list_cond (z : CondTriggerConfig_r16__list_type) : Prop :=
        (seq_cond CondTriggerConfig_r16__root_list (fst z)) /\ (seq_ext_cond CondTriggerConfig_r16__ext_list (snd z)).
Definition CondTriggerConfig_r16__list_format : T_Format CondTriggerConfig_r16__list_type CondTriggerConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format CondTriggerConfig_r16__root_list CondTriggerConfig_r16__root_Format_list CondTriggerConfig_r16__ext_list CondTriggerConfig_r16__ext_Format_list.

Opaque CondTriggerConfig_r16__list_format.
Definition CondTriggerConfig_r16__F1 (z : CondTriggerConfig_r16__Type) : CondTriggerConfig_r16__list_type :=
  (((CondTriggerConfig_r16__condEventId z, (CondTriggerConfig_r16__rsType_r16 z, tt))), (
tt)).
Definition CondTriggerConfig_r16__F2 (y : CondTriggerConfig_r16__list_type) : CondTriggerConfig_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__CondTriggerConfig_r16__Type j0 j1
  end.
Definition CondTriggerConfig_r16__helper1 : (forall a : CondTriggerConfig_r16__Type, CondTriggerConfig_r16__cond a -> CondTriggerConfig_r16__list_cond (CondTriggerConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CondTriggerConfig_r16__helper2 : (forall a : CondTriggerConfig_r16__Type, CondTriggerConfig_r16__F2 (CondTriggerConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CondTriggerConfig_r16__helper3 : (forall b : CondTriggerConfig_r16__list_type, CondTriggerConfig_r16__list_cond b -> CondTriggerConfig_r16__cond (CondTriggerConfig_r16__F2 b) /\ CondTriggerConfig_r16__F1 (CondTriggerConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CondTriggerConfig_r16__cond, CondTriggerConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CondTriggerConfig_r16__Format : T_Format CondTriggerConfig_r16__Type CondTriggerConfig_r16__cond :=
 proj2_format CondTriggerConfig_r16__cond CondTriggerConfig_r16__list_format  CondTriggerConfig_r16__F1 CondTriggerConfig_r16__F2 CondTriggerConfig_r16__helper1 CondTriggerConfig_r16__helper2 CondTriggerConfig_r16__helper3.

Opaque CondTriggerConfig_r16__cond CondTriggerConfig_r16__Format.

