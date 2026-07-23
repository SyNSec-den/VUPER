Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_MeasTriggerQuantity_r16.

Opaque SL_MeasTriggerQuantity_r16__cond SL_MeasTriggerQuantity_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type : Set :=
  make__SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type {
    SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__s1_Threshold_r16 : SL_MeasTriggerQuantity_r16__Type ;
    SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_ReportOnLeave_r16 : bool ;
    SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_Hysteresis_r16 : Hysteresis__Type ;
    SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_TimeToTrigger_r16 : TimeToTrigger__Type ;
}.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_list : list seq_elem := (
 Nor SL_MeasTriggerQuantity_r16__Type SL_MeasTriggerQuantity_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_list : list typ := (
  nil).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond (z : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type) := 
(  SL_MeasTriggerQuantity_r16__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__s1_Threshold_r16 z) /\
  (fun _ => True) (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_ReportOnLeave_r16 z) /\
  Hysteresis__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_Hysteresis_r16 z) /\
  TimeToTrigger__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_TimeToTrigger_r16 z) /\
  True) /\ 
(  True).

Require Import NR.SL_MeasTriggerQuantity_r16.

Opaque SL_MeasTriggerQuantity_r16__cond SL_MeasTriggerQuantity_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type : Set :=
  make__SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type {
    SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__s2_Threshold_r16 : SL_MeasTriggerQuantity_r16__Type ;
    SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_ReportOnLeave_r16 : bool ;
    SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_Hysteresis_r16 : Hysteresis__Type ;
    SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_TimeToTrigger_r16 : TimeToTrigger__Type ;
}.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_list : list seq_elem := (
 Nor SL_MeasTriggerQuantity_r16__Type SL_MeasTriggerQuantity_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_list : list typ := (
  nil).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond (z : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type) := 
(  SL_MeasTriggerQuantity_r16__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__s2_Threshold_r16 z) /\
  (fun _ => True) (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_ReportOnLeave_r16 z) /\
  Hysteresis__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_Hysteresis_r16 z) /\
  TimeToTrigger__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_TimeToTrigger_r16 z) /\
  True) /\ 
(  True).


Inductive SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type : Set :=
  | SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16 : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type -> SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type
  | SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16 : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type -> SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type
.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__list : list typ := (
typ_cons SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond ::
typ_cons SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond ::
 nil).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__cond (c : SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type) := 
  match c with
  | SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16 t => SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond t 
  | SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16 t => SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond t 
  end.

Lemma SL_EventTriggerConfig_r16__sl_EventId_r16__root__len_helper1 : to_bit_sz (length SL_EventTriggerConfig_r16__sl_EventId_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_EventTriggerConfig_r16__sl_EventId_r16__root__len_helper2 : 2 <= length2 SL_EventTriggerConfig_r16__sl_EventId_r16__root__list.
 simpl. lia. Qed.

Definition SL_EventTriggerConfig_r16__sl_EventId_r16__ext__Type : Set := Empty_set.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__ext__cond (c : SL_EventTriggerConfig_r16__sl_EventId_r16__ext__Type) := True.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__Type : Set := SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type + SL_EventTriggerConfig_r16__sl_EventId_r16__ext__Type.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__cond :=
  sum_cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__cond SL_EventTriggerConfig_r16__sl_EventId_r16__ext__cond.
Require Import NR.ReportInterval.

Opaque ReportInterval__cond ReportInterval__Format.

Inductive SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Type : Set :=
 | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r1
 | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r2
 | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r4
 | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r8
 | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r16
 | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r32
 | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r64
 | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__infinity
.
Definition SL_EventTriggerConfig_r16__sl_ReportAmount_r16__cond := (fun (_ : SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Type) => True).
Lemma SL_EventTriggerConfig_r16__sl_ReportAmount_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_EventTriggerConfig_r16__sl_ReportAmount_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_EventTriggerConfig_r16__sl_ReportAmount_r16__nat__helper.

Definition SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F1 t :=
  match t with
  | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r1 => 0
  | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r2 => 1
  | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r4 => 2
  | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r8 => 3
  | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r16 => 4
  | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r32 => 5
  | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r64 => 6
  | SL_EventTriggerConfig_r16__sl_ReportAmount_r16__infinity => 7
  end.
Definition SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F2 n :=
  match n with
  | 0 => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r1
  | 1 => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r2
  | 2 => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r4
  | 3 => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r8
  | 4 => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r16
  | 5 => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r32
  | 6 => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r64
  | 7 => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__infinity
  | _ => SL_EventTriggerConfig_r16__sl_ReportAmount_r16__r1
  end.
Lemma SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F1F2 : forall x : SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Type, (SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F1 x <= 7) /\ SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F2 (SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F1 (SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_MeasReportQuantity_r16.

Opaque SL_MeasReportQuantity_r16__cond SL_MeasReportQuantity_r16__Format.

Require Import NR.SL_RS_Type_r16.

Opaque SL_RS_Type_r16__cond SL_RS_Type_r16__Format.

Record SL_EventTriggerConfig_r16__Type : Set :=
  make__SL_EventTriggerConfig_r16__Type {
    SL_EventTriggerConfig_r16__sl_EventId_r16 : SL_EventTriggerConfig_r16__sl_EventId_r16__Type ;
    SL_EventTriggerConfig_r16__sl_ReportInterval_r16 : ReportInterval__Type ;
    SL_EventTriggerConfig_r16__sl_ReportAmount_r16 : SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Type ;
    SL_EventTriggerConfig_r16__sl_ReportQuantity_r16 : SL_MeasReportQuantity_r16__Type ;
    SL_EventTriggerConfig_r16__sl_RS_Type_r16 : SL_RS_Type_r16__Type ;
}.
Definition SL_EventTriggerConfig_r16__root_list : list seq_elem := (
 Nor SL_EventTriggerConfig_r16__sl_EventId_r16__Type SL_EventTriggerConfig_r16__sl_EventId_r16__cond ::
 Nor ReportInterval__Type ReportInterval__cond ::
 Nor SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Type SL_EventTriggerConfig_r16__sl_ReportAmount_r16__cond ::
 Nor SL_MeasReportQuantity_r16__Type SL_MeasReportQuantity_r16__cond ::
 Nor SL_RS_Type_r16__Type SL_RS_Type_r16__cond ::
 nil).
Definition SL_EventTriggerConfig_r16__ext_list : list typ := (
  nil).
Definition SL_EventTriggerConfig_r16__cond (z : SL_EventTriggerConfig_r16__Type) := 
(  SL_EventTriggerConfig_r16__sl_EventId_r16__cond (SL_EventTriggerConfig_r16__sl_EventId_r16 z) /\
  ReportInterval__cond (SL_EventTriggerConfig_r16__sl_ReportInterval_r16 z) /\
  SL_EventTriggerConfig_r16__sl_ReportAmount_r16__cond (SL_EventTriggerConfig_r16__sl_ReportAmount_r16 z) /\
  SL_MeasReportQuantity_r16__cond (SL_EventTriggerConfig_r16__sl_ReportQuantity_r16 z) /\
  SL_RS_Type_r16__cond (SL_EventTriggerConfig_r16__sl_RS_Type_r16 z) /\
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

Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_Format_Type := Eval cbn in seq_format_prod SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_list.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_Format_list : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_Format_Type :=
  (SL_MeasTriggerQuantity_r16__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).

Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_Format_Type := Eval cbn in get_formats SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_list.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_Format_list : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_Format_Type :=
  unit__Format.

Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_type : Set := (seq_type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_list) * (seq_ext_type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_list).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_cond (z : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_type) : Prop :=
        (seq_cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_list (fst z)) /\ (seq_ext_cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_list (snd z)).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_format : T_Format SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_list SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__root_Format_list SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_list SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__ext_Format_list.

Opaque SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_format.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F1 (z : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type) : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_type :=
  (((SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__s1_Threshold_r16 z, (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_ReportOnLeave_r16 z, (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_Hysteresis_r16 z, (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__sl_TimeToTrigger_r16 z, tt))))), (
tt)).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F2 (y : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_type) : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type j0 j1 j2 j3
  end.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__helper1 : (forall a : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type, SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond a -> SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__helper2 : (forall a : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type, SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F2 (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__helper3 : (forall b : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_type, SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_cond b -> SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F2 b) /\ SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F1 (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond, SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Format : T_Format SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond :=
 proj2_format SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__list_format  SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F1 SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__F2 SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__helper1 SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__helper2 SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__helper3.

Opaque SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Format.


Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_Format_Type := Eval cbn in seq_format_prod SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_list.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_Format_list : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_Format_Type :=
  (SL_MeasTriggerQuantity_r16__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).

Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_Format_Type := Eval cbn in get_formats SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_list.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_Format_list : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_Format_Type :=
  unit__Format.

Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_type : Set := (seq_type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_list) * (seq_ext_type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_list).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_cond (z : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_type) : Prop :=
        (seq_cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_list (fst z)) /\ (seq_ext_cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_list (snd z)).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_format : T_Format SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_list SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__root_Format_list SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_list SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__ext_Format_list.

Opaque SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_format.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F1 (z : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type) : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_type :=
  (((SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__s2_Threshold_r16 z, (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_ReportOnLeave_r16 z, (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_Hysteresis_r16 z, (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__sl_TimeToTrigger_r16 z, tt))))), (
tt)).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F2 (y : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_type) : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type j0 j1 j2 j3
  end.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__helper1 : (forall a : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type, SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond a -> SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__helper2 : (forall a : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type, SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F2 (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__helper3 : (forall b : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_type, SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_cond b -> SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F2 b) /\ SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F1 (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond, SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Format : T_Format SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond :=
 proj2_format SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__list_format  SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F1 SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__F2 SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__helper1 SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__helper2 SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__helper3.

Opaque SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Format.


Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__Format_Type := Eval cbn in get_formats SL_EventTriggerConfig_r16__sl_EventId_r16__root__list.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__Format_list : SL_EventTriggerConfig_r16__sl_EventId_r16__root__Format_Type :=
  (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Format, (SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Format, unit__Format)).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__list__Format := Eval compute in choice_format SL_EventTriggerConfig_r16__sl_EventId_r16__root__list SL_EventTriggerConfig_r16__sl_EventId_r16__root__len_helper1 SL_EventTriggerConfig_r16__sl_EventId_r16__root__len_helper2  SL_EventTriggerConfig_r16__sl_EventId_r16__root__Format_list.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__F1 (z : SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type) : (choice SL_EventTriggerConfig_r16__sl_EventId_r16__root__list) :=
  match z with
   | SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16 t => existT _ 0 t
  | SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16 t => existT _ 1 t
  end.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__g := (fun n => typ_set (get_nth_typ SL_EventTriggerConfig_r16__sl_EventId_r16__root__list n)).
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__F2 (y : choice SL_EventTriggerConfig_r16__sl_EventId_r16__root__list) : SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_EventTriggerConfig_r16__sl_EventId_r16__root__g n -> SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type) with
    | 0 => fun (t : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16__Type) => SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS1_r16 t 
    | 1 => fun (t : SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16__Type) => SL_EventTriggerConfig_r16__sl_EventId_r16__root__eventS2_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_EventTriggerConfig_r16__sl_EventId_r16__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_EventTriggerConfig_r16__sl_EventId_r16__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_EventTriggerConfig_r16__sl_EventId_r16__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type with end) n0
           end t0).

Lemma SL_EventTriggerConfig_r16__sl_EventId_r16__root__helper2 :  forall (y : SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type), SL_EventTriggerConfig_r16__sl_EventId_r16__root__cond y -> choice_cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__list (SL_EventTriggerConfig_r16__sl_EventId_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_EventTriggerConfig_r16__sl_EventId_r16__root__helper3 :  forall (y : SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type), SL_EventTriggerConfig_r16__sl_EventId_r16__root__F2 (SL_EventTriggerConfig_r16__sl_EventId_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_EventTriggerConfig_r16__sl_EventId_r16__root__helper4 : (forall b : choice SL_EventTriggerConfig_r16__sl_EventId_r16__root__list, choice_cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__list b -> SL_EventTriggerConfig_r16__sl_EventId_r16__root__cond (SL_EventTriggerConfig_r16__sl_EventId_r16__root__F2 b) /\ SL_EventTriggerConfig_r16__sl_EventId_r16__root__F1 (SL_EventTriggerConfig_r16__sl_EventId_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_EventTriggerConfig_r16__sl_EventId_r16__root__F1 SL_EventTriggerConfig_r16__sl_EventId_r16__root__F2.
Definition SL_EventTriggerConfig_r16__sl_EventId_r16__root__Format : T_Format SL_EventTriggerConfig_r16__sl_EventId_r16__root__Type SL_EventTriggerConfig_r16__sl_EventId_r16__root__cond :=
  (* Eval compute in *) proj2_format SL_EventTriggerConfig_r16__sl_EventId_r16__root__cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__list__Format SL_EventTriggerConfig_r16__sl_EventId_r16__root__F1 SL_EventTriggerConfig_r16__sl_EventId_r16__root__F2 SL_EventTriggerConfig_r16__sl_EventId_r16__root__helper2 SL_EventTriggerConfig_r16__sl_EventId_r16__root__helper3 SL_EventTriggerConfig_r16__sl_EventId_r16__root__helper4.
Opaque SL_EventTriggerConfig_r16__sl_EventId_r16__root__cond SL_EventTriggerConfig_r16__sl_EventId_r16__root__Format.

Definition SL_EventTriggerConfig_r16__sl_EventId_r16__ext__Format : T_Format SL_EventTriggerConfig_r16__sl_EventId_r16__ext__Type SL_EventTriggerConfig_r16__sl_EventId_r16__ext__cond := empty_format.
Opaque SL_EventTriggerConfig_r16__sl_EventId_r16__ext__cond SL_EventTriggerConfig_r16__sl_EventId_r16__ext__Format.

Definition SL_EventTriggerConfig_r16__sl_EventId_r16__Format : T_Format SL_EventTriggerConfig_r16__sl_EventId_r16__Type SL_EventTriggerConfig_r16__sl_EventId_r16__cond := sum_format SL_EventTriggerConfig_r16__sl_EventId_r16__root__Format SL_EventTriggerConfig_r16__sl_EventId_r16__ext__Format.
Opaque SL_EventTriggerConfig_r16__sl_EventId_r16__cond SL_EventTriggerConfig_r16__sl_EventId_r16__Format.

Definition SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Format : T_Format SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_EventTriggerConfig_r16__sl_ReportAmount_r16__nat__Format SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F1 SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F2 SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F1F2 SL_EventTriggerConfig_r16__sl_ReportAmount_r16__F2F1.

Opaque SL_EventTriggerConfig_r16__sl_ReportAmount_r16__cond SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Format.


Definition SL_EventTriggerConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_EventTriggerConfig_r16__root_list.
Definition SL_EventTriggerConfig_r16__root_Format_list : SL_EventTriggerConfig_r16__root_Format_Type :=
  (SL_EventTriggerConfig_r16__sl_EventId_r16__Format, (ReportInterval__Format, (SL_EventTriggerConfig_r16__sl_ReportAmount_r16__Format, (SL_MeasReportQuantity_r16__Format, (SL_RS_Type_r16__Format, unit_format))))).

Definition SL_EventTriggerConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_EventTriggerConfig_r16__ext_list.
Definition SL_EventTriggerConfig_r16__ext_Format_list : SL_EventTriggerConfig_r16__ext_Format_Type :=
  unit__Format.

Definition SL_EventTriggerConfig_r16__list_type : Set := (seq_type SL_EventTriggerConfig_r16__root_list) * (seq_ext_type SL_EventTriggerConfig_r16__ext_list).
Definition SL_EventTriggerConfig_r16__list_cond (z : SL_EventTriggerConfig_r16__list_type) : Prop :=
        (seq_cond SL_EventTriggerConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_EventTriggerConfig_r16__ext_list (snd z)).
Definition SL_EventTriggerConfig_r16__list_format : T_Format SL_EventTriggerConfig_r16__list_type SL_EventTriggerConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_EventTriggerConfig_r16__root_list SL_EventTriggerConfig_r16__root_Format_list SL_EventTriggerConfig_r16__ext_list SL_EventTriggerConfig_r16__ext_Format_list.

Opaque SL_EventTriggerConfig_r16__list_format.
Definition SL_EventTriggerConfig_r16__F1 (z : SL_EventTriggerConfig_r16__Type) : SL_EventTriggerConfig_r16__list_type :=
  (((SL_EventTriggerConfig_r16__sl_EventId_r16 z, (SL_EventTriggerConfig_r16__sl_ReportInterval_r16 z, (SL_EventTriggerConfig_r16__sl_ReportAmount_r16 z, (SL_EventTriggerConfig_r16__sl_ReportQuantity_r16 z, (SL_EventTriggerConfig_r16__sl_RS_Type_r16 z, tt)))))), (
tt)).
Definition SL_EventTriggerConfig_r16__F2 (y : SL_EventTriggerConfig_r16__list_type) : SL_EventTriggerConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__SL_EventTriggerConfig_r16__Type j0 j1 j2 j3 j4
  end.
Definition SL_EventTriggerConfig_r16__helper1 : (forall a : SL_EventTriggerConfig_r16__Type, SL_EventTriggerConfig_r16__cond a -> SL_EventTriggerConfig_r16__list_cond (SL_EventTriggerConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_EventTriggerConfig_r16__helper2 : (forall a : SL_EventTriggerConfig_r16__Type, SL_EventTriggerConfig_r16__F2 (SL_EventTriggerConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_EventTriggerConfig_r16__helper3 : (forall b : SL_EventTriggerConfig_r16__list_type, SL_EventTriggerConfig_r16__list_cond b -> SL_EventTriggerConfig_r16__cond (SL_EventTriggerConfig_r16__F2 b) /\ SL_EventTriggerConfig_r16__F1 (SL_EventTriggerConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_EventTriggerConfig_r16__cond, SL_EventTriggerConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_EventTriggerConfig_r16__Format : T_Format SL_EventTriggerConfig_r16__Type SL_EventTriggerConfig_r16__cond :=
 proj2_format SL_EventTriggerConfig_r16__cond SL_EventTriggerConfig_r16__list_format  SL_EventTriggerConfig_r16__F1 SL_EventTriggerConfig_r16__F2 SL_EventTriggerConfig_r16__helper1 SL_EventTriggerConfig_r16__helper2 SL_EventTriggerConfig_r16__helper3.

Opaque SL_EventTriggerConfig_r16__cond SL_EventTriggerConfig_r16__Format.

