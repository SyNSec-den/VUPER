Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.AreaConfiguration_r16.

Opaque AreaConfiguration_r16__cond AreaConfiguration_r16__Format.

Require Import NR.BT_NameList_r16.

Opaque BT_NameList_r16__cond BT_NameList_r16__Format.

Require Import NR.WLAN_NameList_r16.

Opaque WLAN_NameList_r16__cond WLAN_NameList_r16__Format.

Require Import NR.Sensor_NameList_r16.

Opaque Sensor_NameList_r16__cond Sensor_NameList_r16__Format.

Require Import NR.LoggingDuration_r16.

Opaque LoggingDuration_r16__cond LoggingDuration_r16__Format.

Require Import NR.LoggedPeriodicalReportConfig_r16.

Opaque LoggedPeriodicalReportConfig_r16__cond LoggedPeriodicalReportConfig_r16__Format.

Require Import NR.LoggedEventTriggerConfig_r16.

Opaque LoggedEventTriggerConfig_r16__cond LoggedEventTriggerConfig_r16__Format.


Inductive VarLogMeasConfig_r16_IEs__reportType__Type : Set :=
  | VarLogMeasConfig_r16_IEs__reportType__periodical : LoggedPeriodicalReportConfig_r16__Type -> VarLogMeasConfig_r16_IEs__reportType__Type
  | VarLogMeasConfig_r16_IEs__reportType__eventTriggered : LoggedEventTriggerConfig_r16__Type -> VarLogMeasConfig_r16_IEs__reportType__Type
.
Definition VarLogMeasConfig_r16_IEs__reportType__list : list typ := (
typ_cons LoggedPeriodicalReportConfig_r16__Type LoggedPeriodicalReportConfig_r16__cond ::
typ_cons LoggedEventTriggerConfig_r16__Type LoggedEventTriggerConfig_r16__cond ::
 nil).
Definition VarLogMeasConfig_r16_IEs__reportType__cond (c : VarLogMeasConfig_r16_IEs__reportType__Type) := 
  match c with
  | VarLogMeasConfig_r16_IEs__reportType__periodical t => LoggedPeriodicalReportConfig_r16__cond t 
  | VarLogMeasConfig_r16_IEs__reportType__eventTriggered t => LoggedEventTriggerConfig_r16__cond t 
  end.

Lemma VarLogMeasConfig_r16_IEs__reportType__len_helper1 : to_bit_sz (length VarLogMeasConfig_r16_IEs__reportType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma VarLogMeasConfig_r16_IEs__reportType__len_helper2 : 2 <= length2 VarLogMeasConfig_r16_IEs__reportType__list.
 simpl. lia. Qed.
Inductive VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Type : Set :=
 | VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__true
.
Definition VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__cond := (fun (_ : VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Type) => True).
Lemma VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__nat__helper.

Definition VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F1 t :=
  match t with
  | VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__true => 0
  end.
Definition VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F2 n :=
  match n with
  | 0 => VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__true
  | _ => VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__true
  end.
Lemma VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F1F2 : forall x : VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Type, (VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F1 x <= 0) /\ VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F2 (VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F1 x) = x. imp_solve. Qed.
Lemma VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F2F1 : forall (y : nat) (H : y <= 0), VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F1 (VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.AreaConfiguration_v1700.

Opaque AreaConfiguration_v1700__cond AreaConfiguration_v1700__Format.

Record VarLogMeasConfig_r16_IEs__Type : Set :=
  make__VarLogMeasConfig_r16_IEs__Type {
    VarLogMeasConfig_r16_IEs__areaConfiguration_r16 : option AreaConfiguration_r16__Type ;
    VarLogMeasConfig_r16_IEs__bt_NameList_r16 : option BT_NameList_r16__Type ;
    VarLogMeasConfig_r16_IEs__wlan_NameList_r16 : option WLAN_NameList_r16__Type ;
    VarLogMeasConfig_r16_IEs__sensor_NameList_r16 : option Sensor_NameList_r16__Type ;
    VarLogMeasConfig_r16_IEs__loggingDuration_r16 : LoggingDuration_r16__Type ;
    VarLogMeasConfig_r16_IEs__reportType : VarLogMeasConfig_r16_IEs__reportType__Type ;
    VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17 : option VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Type ;
    VarLogMeasConfig_r16_IEs__areaConfiguration_v1700 : option AreaConfiguration_v1700__Type ;
}.
Definition VarLogMeasConfig_r16_IEs__list := (
 Opt AreaConfiguration_r16__Type AreaConfiguration_r16__cond ::
 Opt BT_NameList_r16__Type BT_NameList_r16__cond ::
 Opt WLAN_NameList_r16__Type WLAN_NameList_r16__cond ::
 Opt Sensor_NameList_r16__Type Sensor_NameList_r16__cond ::
 Nor LoggingDuration_r16__Type LoggingDuration_r16__cond ::
 Nor VarLogMeasConfig_r16_IEs__reportType__Type VarLogMeasConfig_r16_IEs__reportType__cond ::
 Opt VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Type VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__cond ::
 Opt AreaConfiguration_v1700__Type AreaConfiguration_v1700__cond ::
 nil).
Definition VarLogMeasConfig_r16_IEs__cond z := 
  opt_cond AreaConfiguration_r16__cond (VarLogMeasConfig_r16_IEs__areaConfiguration_r16 z) /\
  opt_cond BT_NameList_r16__cond (VarLogMeasConfig_r16_IEs__bt_NameList_r16 z) /\
  opt_cond WLAN_NameList_r16__cond (VarLogMeasConfig_r16_IEs__wlan_NameList_r16 z) /\
  opt_cond Sensor_NameList_r16__cond (VarLogMeasConfig_r16_IEs__sensor_NameList_r16 z) /\
  LoggingDuration_r16__cond (VarLogMeasConfig_r16_IEs__loggingDuration_r16 z) /\
  VarLogMeasConfig_r16_IEs__reportType__cond (VarLogMeasConfig_r16_IEs__reportType z) /\
  opt_cond VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__cond (VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17 z) /\
  opt_cond AreaConfiguration_v1700__cond (VarLogMeasConfig_r16_IEs__areaConfiguration_v1700 z) /\
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

Definition VarLogMeasConfig_r16_IEs__reportType__Format_Type := Eval cbn in get_formats VarLogMeasConfig_r16_IEs__reportType__list.
Definition VarLogMeasConfig_r16_IEs__reportType__Format_list : VarLogMeasConfig_r16_IEs__reportType__Format_Type :=
  (LoggedPeriodicalReportConfig_r16__Format, (LoggedEventTriggerConfig_r16__Format, unit__Format)).
Definition VarLogMeasConfig_r16_IEs__reportType__list__Format := Eval compute in choice_format VarLogMeasConfig_r16_IEs__reportType__list VarLogMeasConfig_r16_IEs__reportType__len_helper1 VarLogMeasConfig_r16_IEs__reportType__len_helper2  VarLogMeasConfig_r16_IEs__reportType__Format_list.
Definition VarLogMeasConfig_r16_IEs__reportType__F1 (z : VarLogMeasConfig_r16_IEs__reportType__Type) : (choice VarLogMeasConfig_r16_IEs__reportType__list) :=
  match z with
   | VarLogMeasConfig_r16_IEs__reportType__periodical t => existT _ 0 t
  | VarLogMeasConfig_r16_IEs__reportType__eventTriggered t => existT _ 1 t
  end.
Definition VarLogMeasConfig_r16_IEs__reportType__g := (fun n => typ_set (get_nth_typ VarLogMeasConfig_r16_IEs__reportType__list n)).
Definition VarLogMeasConfig_r16_IEs__reportType__F2 (y : choice VarLogMeasConfig_r16_IEs__reportType__list) : VarLogMeasConfig_r16_IEs__reportType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (VarLogMeasConfig_r16_IEs__reportType__g n -> VarLogMeasConfig_r16_IEs__reportType__Type) with
    | 0 => fun (t : LoggedPeriodicalReportConfig_r16__Type) => VarLogMeasConfig_r16_IEs__reportType__periodical t 
    | 1 => fun (t : LoggedEventTriggerConfig_r16__Type) => VarLogMeasConfig_r16_IEs__reportType__eventTriggered t 
 | (S (S n0)) => (fun (x' : nat) (t'' : VarLogMeasConfig_r16_IEs__reportType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ VarLogMeasConfig_r16_IEs__reportType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len VarLogMeasConfig_r16_IEs__reportType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return VarLogMeasConfig_r16_IEs__reportType__Type with end) n0
           end t0).

Lemma VarLogMeasConfig_r16_IEs__reportType__helper2 :  forall (y : VarLogMeasConfig_r16_IEs__reportType__Type), VarLogMeasConfig_r16_IEs__reportType__cond y -> choice_cond VarLogMeasConfig_r16_IEs__reportType__list (VarLogMeasConfig_r16_IEs__reportType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma VarLogMeasConfig_r16_IEs__reportType__helper3 :  forall (y : VarLogMeasConfig_r16_IEs__reportType__Type), VarLogMeasConfig_r16_IEs__reportType__F2 (VarLogMeasConfig_r16_IEs__reportType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma VarLogMeasConfig_r16_IEs__reportType__helper4 : (forall b : choice VarLogMeasConfig_r16_IEs__reportType__list, choice_cond VarLogMeasConfig_r16_IEs__reportType__list b -> VarLogMeasConfig_r16_IEs__reportType__cond (VarLogMeasConfig_r16_IEs__reportType__F2 b) /\ VarLogMeasConfig_r16_IEs__reportType__F1 (VarLogMeasConfig_r16_IEs__reportType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length VarLogMeasConfig_r16_IEs__reportType__F1 VarLogMeasConfig_r16_IEs__reportType__F2.
Definition VarLogMeasConfig_r16_IEs__reportType__Format : T_Format VarLogMeasConfig_r16_IEs__reportType__Type VarLogMeasConfig_r16_IEs__reportType__cond :=
  (* Eval compute in *) proj2_format VarLogMeasConfig_r16_IEs__reportType__cond VarLogMeasConfig_r16_IEs__reportType__list__Format VarLogMeasConfig_r16_IEs__reportType__F1 VarLogMeasConfig_r16_IEs__reportType__F2 VarLogMeasConfig_r16_IEs__reportType__helper2 VarLogMeasConfig_r16_IEs__reportType__helper3 VarLogMeasConfig_r16_IEs__reportType__helper4.
Opaque VarLogMeasConfig_r16_IEs__reportType__cond VarLogMeasConfig_r16_IEs__reportType__Format.

Definition VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Format : T_Format VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__nat__Format VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F1 VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F2 VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F1F2 VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__F2F1.

Opaque VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__cond VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Format.


Definition VarLogMeasConfig_r16_IEs__Format_Type := Eval cbn in seq_format_prod VarLogMeasConfig_r16_IEs__list.
Definition VarLogMeasConfig_r16_IEs__Format_list : VarLogMeasConfig_r16_IEs__Format_Type :=
  (AreaConfiguration_r16__Format, (BT_NameList_r16__Format, (WLAN_NameList_r16__Format, (Sensor_NameList_r16__Format, (LoggingDuration_r16__Format, (VarLogMeasConfig_r16_IEs__reportType__Format, (VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17__Format, (AreaConfiguration_v1700__Format, unit_format)))))))).
Definition VarLogMeasConfig_r16_IEs__list__Format := (*Eval compute in *) seq_format VarLogMeasConfig_r16_IEs__list VarLogMeasConfig_r16_IEs__Format_list.
Definition VarLogMeasConfig_r16_IEs__F1 z :=
  (VarLogMeasConfig_r16_IEs__areaConfiguration_r16 z, (VarLogMeasConfig_r16_IEs__bt_NameList_r16 z, (VarLogMeasConfig_r16_IEs__wlan_NameList_r16 z, (VarLogMeasConfig_r16_IEs__sensor_NameList_r16 z, (VarLogMeasConfig_r16_IEs__loggingDuration_r16 z, (VarLogMeasConfig_r16_IEs__reportType z, (VarLogMeasConfig_r16_IEs__earlyMeasIndication_r17 z, (VarLogMeasConfig_r16_IEs__areaConfiguration_v1700 z, tt)))))))).
Definition VarLogMeasConfig_r16_IEs__F2 (y : seq_type VarLogMeasConfig_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__VarLogMeasConfig_r16_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma VarLogMeasConfig_r16_IEs__F1F2_cond (z : VarLogMeasConfig_r16_IEs__Type)
  : VarLogMeasConfig_r16_IEs__cond z ->
  (seq_cond VarLogMeasConfig_r16_IEs__list (VarLogMeasConfig_r16_IEs__F1 z)).
intro H. unfold VarLogMeasConfig_r16_IEs__cond in H. simpl. auto. Qed.
Lemma VarLogMeasConfig_r16_IEs__F1F2_cond2 (z : VarLogMeasConfig_r16_IEs__Type)
 : VarLogMeasConfig_r16_IEs__F2 (VarLogMeasConfig_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarLogMeasConfig_r16_IEs__F2F1_cond (y : seq_type VarLogMeasConfig_r16_IEs__list)
  : seq_cond VarLogMeasConfig_r16_IEs__list y ->
 (VarLogMeasConfig_r16_IEs__cond (VarLogMeasConfig_r16_IEs__F2 y)) /\  VarLogMeasConfig_r16_IEs__F1 (VarLogMeasConfig_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarLogMeasConfig_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold VarLogMeasConfig_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarLogMeasConfig_r16_IEs__Format : T_Format VarLogMeasConfig_r16_IEs__Type VarLogMeasConfig_r16_IEs__cond :=
        proj2_format  VarLogMeasConfig_r16_IEs__cond VarLogMeasConfig_r16_IEs__list__Format
    VarLogMeasConfig_r16_IEs__F1 VarLogMeasConfig_r16_IEs__F2 VarLogMeasConfig_r16_IEs__F1F2_cond  VarLogMeasConfig_r16_IEs__F1F2_cond2 VarLogMeasConfig_r16_IEs__F2F1_cond.
Opaque VarLogMeasConfig_r16_IEs__cond VarLogMeasConfig_r16_IEs__Format.

