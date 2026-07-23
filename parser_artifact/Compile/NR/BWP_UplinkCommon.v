Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BWP.

Opaque BWP__cond BWP__Format.

Require Import NR.SetupRelease.
Require Import NR.RACH_ConfigCommon.
Definition BWP_UplinkCommon__rach_ConfigCommon__Type := SetupRelease__Type RACH_ConfigCommon__Type.
Definition BWP_UplinkCommon__rach_ConfigCommon__cond := SetupRelease__cond _ RACH_ConfigCommon__cond.
Definition BWP_UplinkCommon__rach_ConfigCommon__Format : T_Format BWP_UplinkCommon__rach_ConfigCommon__Type BWP_UplinkCommon__rach_ConfigCommon__cond := SetupRelease__Format _ _ RACH_ConfigCommon__Format.
Opaque BWP_UplinkCommon__rach_ConfigCommon__cond BWP_UplinkCommon__rach_ConfigCommon__Format.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_ConfigCommon.
Definition BWP_UplinkCommon__pusch_ConfigCommon__Type := SetupRelease__Type PUSCH_ConfigCommon__Type.
Definition BWP_UplinkCommon__pusch_ConfigCommon__cond := SetupRelease__cond _ PUSCH_ConfigCommon__cond.
Definition BWP_UplinkCommon__pusch_ConfigCommon__Format : T_Format BWP_UplinkCommon__pusch_ConfigCommon__Type BWP_UplinkCommon__pusch_ConfigCommon__cond := SetupRelease__Format _ _ PUSCH_ConfigCommon__Format.
Opaque BWP_UplinkCommon__pusch_ConfigCommon__cond BWP_UplinkCommon__pusch_ConfigCommon__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_ConfigCommon.
Definition BWP_UplinkCommon__pucch_ConfigCommon__Type := SetupRelease__Type PUCCH_ConfigCommon__Type.
Definition BWP_UplinkCommon__pucch_ConfigCommon__cond := SetupRelease__cond _ PUCCH_ConfigCommon__cond.
Definition BWP_UplinkCommon__pucch_ConfigCommon__Format : T_Format BWP_UplinkCommon__pucch_ConfigCommon__Type BWP_UplinkCommon__pucch_ConfigCommon__cond := SetupRelease__Format _ _ PUCCH_ConfigCommon__Format.
Opaque BWP_UplinkCommon__pucch_ConfigCommon__cond BWP_UplinkCommon__pucch_ConfigCommon__Format.

Require Import NR.SetupRelease.
Require Import NR.RACH_ConfigCommon.
Definition BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__Type := SetupRelease__Type RACH_ConfigCommon__Type.
Definition BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__cond := SetupRelease__cond _ RACH_ConfigCommon__cond.
Definition BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__Format : T_Format BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__Type BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__cond := SetupRelease__Format _ _ RACH_ConfigCommon__Format.
Opaque BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__cond BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__Format.

Inductive BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Type : Set :=
 | BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__enabled
.
Definition BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__cond := (fun (_ : BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Type) => True).
Lemma BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__nat__helper.

Definition BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F1 t :=
  match t with
  | BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__enabled => 0
  end.
Definition BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F2 n :=
  match n with
  | 0 => BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__enabled
  | _ => BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__enabled
  end.
Lemma BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F1F2 : forall x : BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Type, (BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F1 x <= 0) /\ BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F2 (BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F1 (BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.MsgA_ConfigCommon_r16.
Definition BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__Type := SetupRelease__Type MsgA_ConfigCommon_r16__Type.
Definition BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__cond := SetupRelease__cond _ MsgA_ConfigCommon_r16__cond.
Definition BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__Format : T_Format BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__Type BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__cond := SetupRelease__Format _ _ MsgA_ConfigCommon_r16__Format.
Opaque BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__cond BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__Format.

Record BWP_UplinkCommon__ext0O__Type : Set :=
  make__BWP_UplinkCommon__ext0O__Type {
    BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16 : option BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__Type ;
    BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16 : option BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Type ;
    BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16 : option BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__Type ;
}.
Definition BWP_UplinkCommon__ext0O__list := (
 Opt BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__Type BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__cond ::
 Opt BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Type BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__cond ::
 Opt BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__Type BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__cond ::
 nil).
Definition BWP_UplinkCommon__ext0O__cond z := 
  opt_cond BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__cond (BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16 z) /\
  opt_cond BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__cond (BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16 z) /\
  opt_cond BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__cond (BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16 z) /\
  True.

Definition BWP_UplinkCommon__ext0__Type := BWP_UplinkCommon__ext0O__Type.
Definition BWP_UplinkCommon__ext0__cond := BWP_UplinkCommon__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.AdditionalRACH_ConfigList_r17.
Definition BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__Type := SetupRelease__Type AdditionalRACH_ConfigList_r17__Type.
Definition BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__cond := SetupRelease__cond _ AdditionalRACH_ConfigList_r17__cond.
Definition BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__Format : T_Format BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__Type BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__cond := SetupRelease__Format _ _ AdditionalRACH_ConfigList_r17__Format.
Opaque BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__cond BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.NumberOfMsg3_Repetitions_r17.

Opaque NumberOfMsg3_Repetitions_r17__cond NumberOfMsg3_Repetitions_r17__Format.

Definition BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__Type := list NumberOfMsg3_Repetitions_r17__Type.

Definition BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__cond (z : BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__Type) := (list_and NumberOfMsg3_Repetitions_r17__cond z) /\ (length z = Z.to_nat 4).

Lemma BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__Type := Z.
Definition BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__cond := (fun z => (0 <= z <= 31)%Z).
Definition BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__Type := list Z.

Definition BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__cond (z : BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__Type) := (list_and BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__cond z) /\ (length z = Z.to_nat 8).

Record BWP_UplinkCommon__ext1O__Type : Set :=
  make__BWP_UplinkCommon__ext1O__Type {
    BWP_UplinkCommon__ext1O__enableRA_PrioritizationForSlicing_r17 : option bool ;
    BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17 : option BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__Type ;
    BWP_UplinkCommon__ext1O__rsrp_ThresholdMsg3_r17 : option RSRP_Range__Type ;
    BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17 : option BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__Type ;
    BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17 : option BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__Type ;
}.
Definition BWP_UplinkCommon__ext1O__list := (
 Opt bool (fun _ => True) ::
 Opt BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__Type BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__Type BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__cond ::
 Opt BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__Type BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__cond ::
 nil).
Definition BWP_UplinkCommon__ext1O__cond z := 
  opt_cond (fun _ => True) (BWP_UplinkCommon__ext1O__enableRA_PrioritizationForSlicing_r17 z) /\
  opt_cond BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__cond (BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17 z) /\
  opt_cond RSRP_Range__cond (BWP_UplinkCommon__ext1O__rsrp_ThresholdMsg3_r17 z) /\
  opt_cond BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__cond (BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17 z) /\
  opt_cond BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__cond (BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17 z) /\
  True.

Definition BWP_UplinkCommon__ext1__Type := BWP_UplinkCommon__ext1O__Type.
Definition BWP_UplinkCommon__ext1__cond := BWP_UplinkCommon__ext1O__cond.

Record BWP_UplinkCommon__Type : Set :=
  make__BWP_UplinkCommon__Type {
    BWP_UplinkCommon__genericParameters : BWP__Type ;
    BWP_UplinkCommon__rach_ConfigCommon : option BWP_UplinkCommon__rach_ConfigCommon__Type ;
    BWP_UplinkCommon__pusch_ConfigCommon : option BWP_UplinkCommon__pusch_ConfigCommon__Type ;
    BWP_UplinkCommon__pucch_ConfigCommon : option BWP_UplinkCommon__pucch_ConfigCommon__Type ;
    BWP_UplinkCommon__ext0 : option BWP_UplinkCommon__ext0__Type ;
    BWP_UplinkCommon__ext1 : option BWP_UplinkCommon__ext1__Type ;
}.
Definition BWP_UplinkCommon__root_list : list seq_elem := (
 Nor BWP__Type BWP__cond ::
 Opt BWP_UplinkCommon__rach_ConfigCommon__Type BWP_UplinkCommon__rach_ConfigCommon__cond ::
 Opt BWP_UplinkCommon__pusch_ConfigCommon__Type BWP_UplinkCommon__pusch_ConfigCommon__cond ::
 Opt BWP_UplinkCommon__pucch_ConfigCommon__Type BWP_UplinkCommon__pucch_ConfigCommon__cond ::
 nil).
Definition BWP_UplinkCommon__ext_list : list typ := (
  typ_cons BWP_UplinkCommon__ext0__Type BWP_UplinkCommon__ext0__cond ::
  typ_cons BWP_UplinkCommon__ext1__Type BWP_UplinkCommon__ext1__cond ::
  nil).
Definition BWP_UplinkCommon__cond (z : BWP_UplinkCommon__Type) := 
(  BWP__cond (BWP_UplinkCommon__genericParameters z) /\
  opt_cond BWP_UplinkCommon__rach_ConfigCommon__cond (BWP_UplinkCommon__rach_ConfigCommon z) /\
  opt_cond BWP_UplinkCommon__pusch_ConfigCommon__cond (BWP_UplinkCommon__pusch_ConfigCommon z) /\
  opt_cond BWP_UplinkCommon__pucch_ConfigCommon__cond (BWP_UplinkCommon__pucch_ConfigCommon z) /\
  True) /\ 
(  opt_cond BWP_UplinkCommon__ext0__cond (BWP_UplinkCommon__ext0 z) /\
  opt_cond BWP_UplinkCommon__ext1__cond (BWP_UplinkCommon__ext1 z) /\
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
Opaque BWP_UplinkCommon__rach_ConfigCommon__cond BWP_UplinkCommon__rach_ConfigCommon__Format.

Opaque BWP_UplinkCommon__pusch_ConfigCommon__cond BWP_UplinkCommon__pusch_ConfigCommon__Format.

Opaque BWP_UplinkCommon__pucch_ConfigCommon__cond BWP_UplinkCommon__pucch_ConfigCommon__Format.

Opaque BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__cond BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__Format.

Definition BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Format : T_Format BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__nat__Format BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F1 BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F2 BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F1F2 BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__F2F1.

Opaque BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__cond BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Format.

Opaque BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__cond BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__Format.


Definition BWP_UplinkCommon__ext0O__Format_Type := Eval cbn in seq_format_prod BWP_UplinkCommon__ext0O__list.
Definition BWP_UplinkCommon__ext0O__Format_list : BWP_UplinkCommon__ext0O__Format_Type :=
  (BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16__Format, (BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16__Format, (BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16__Format, unit_format))).
Definition BWP_UplinkCommon__ext0O__list__Format := (*Eval compute in *) seq_format BWP_UplinkCommon__ext0O__list BWP_UplinkCommon__ext0O__Format_list.
Definition BWP_UplinkCommon__ext0O__F1 z :=
  (BWP_UplinkCommon__ext0O__rach_ConfigCommonIAB_r16 z, (BWP_UplinkCommon__ext0O__useInterlacePUCCH_PUSCH_r16 z, (BWP_UplinkCommon__ext0O__msgA_ConfigCommon_r16 z, tt))).
Definition BWP_UplinkCommon__ext0O__F2 (y : seq_type BWP_UplinkCommon__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BWP_UplinkCommon__ext0O__Type i0 i1 i2
  end.
Lemma BWP_UplinkCommon__ext0O__F1F2_cond (z : BWP_UplinkCommon__ext0O__Type)
  : BWP_UplinkCommon__ext0O__cond z ->
  (seq_cond BWP_UplinkCommon__ext0O__list (BWP_UplinkCommon__ext0O__F1 z)).
intro H. unfold BWP_UplinkCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma BWP_UplinkCommon__ext0O__F1F2_cond2 (z : BWP_UplinkCommon__ext0O__Type)
 : BWP_UplinkCommon__ext0O__F2 (BWP_UplinkCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_UplinkCommon__ext0O__F2F1_cond (y : seq_type BWP_UplinkCommon__ext0O__list)
  : seq_cond BWP_UplinkCommon__ext0O__list y ->
 (BWP_UplinkCommon__ext0O__cond (BWP_UplinkCommon__ext0O__F2 y)) /\  BWP_UplinkCommon__ext0O__F1 (BWP_UplinkCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_UplinkCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold BWP_UplinkCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_UplinkCommon__ext0O__Format : T_Format BWP_UplinkCommon__ext0O__Type BWP_UplinkCommon__ext0O__cond :=
        proj2_format  BWP_UplinkCommon__ext0O__cond BWP_UplinkCommon__ext0O__list__Format
    BWP_UplinkCommon__ext0O__F1 BWP_UplinkCommon__ext0O__F2 BWP_UplinkCommon__ext0O__F1F2_cond  BWP_UplinkCommon__ext0O__F1F2_cond2 BWP_UplinkCommon__ext0O__F2F1_cond.
Opaque BWP_UplinkCommon__ext0O__cond BWP_UplinkCommon__ext0O__Format.

Definition BWP_UplinkCommon__ext0__check_all_none (b : BWP_UplinkCommon__ext0O__Type) : bool :=
match b with 
  | make__BWP_UplinkCommon__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition BWP_UplinkCommon__ext0__Format : T_Format BWP_UplinkCommon__ext0__Type BWP_UplinkCommon__ext0__cond :=
  restrict_add_format BWP_UplinkCommon__ext0__check_all_none BWP_UplinkCommon__ext0O__Format.

Opaque BWP_UplinkCommon__ext0__cond BWP_UplinkCommon__ext0__Format.

Opaque BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__cond BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__Format.

Definition BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__Format : T_Format BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__Type BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__cond := seq_of_fixed_format NumberOfMsg3_Repetitions_r17__Format 4.

Opaque BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__cond BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__Format.

Definition BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__Format : T_Format Z BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__cond :=
 ranged_int_format (0) (31) BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__helper1 BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__helper2.

Opaque BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__cond BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__Format.

Definition BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__Format : T_Format BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__Type BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__cond := seq_of_fixed_format BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__seq_of__Format 8.

Opaque BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__cond BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__Format.


Definition BWP_UplinkCommon__ext1O__Format_Type := Eval cbn in seq_format_prod BWP_UplinkCommon__ext1O__list.
Definition BWP_UplinkCommon__ext1O__Format_list : BWP_UplinkCommon__ext1O__Format_Type :=
  (bool__Format, (BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17__Format, (RSRP_Range__Format, (BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17__Format, (BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17__Format, unit_format))))).
Definition BWP_UplinkCommon__ext1O__list__Format := (*Eval compute in *) seq_format BWP_UplinkCommon__ext1O__list BWP_UplinkCommon__ext1O__Format_list.
Definition BWP_UplinkCommon__ext1O__F1 z :=
  (BWP_UplinkCommon__ext1O__enableRA_PrioritizationForSlicing_r17 z, (BWP_UplinkCommon__ext1O__additionalRACH_ConfigList_r17 z, (BWP_UplinkCommon__ext1O__rsrp_ThresholdMsg3_r17 z, (BWP_UplinkCommon__ext1O__numberOfMsg3_RepetitionsList_r17 z, (BWP_UplinkCommon__ext1O__mcs_Msg3_Repetitions_r17 z, tt))))).
Definition BWP_UplinkCommon__ext1O__F2 (y : seq_type BWP_UplinkCommon__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__BWP_UplinkCommon__ext1O__Type i0 i1 i2 i3 i4
  end.
Lemma BWP_UplinkCommon__ext1O__F1F2_cond (z : BWP_UplinkCommon__ext1O__Type)
  : BWP_UplinkCommon__ext1O__cond z ->
  (seq_cond BWP_UplinkCommon__ext1O__list (BWP_UplinkCommon__ext1O__F1 z)).
intro H. unfold BWP_UplinkCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma BWP_UplinkCommon__ext1O__F1F2_cond2 (z : BWP_UplinkCommon__ext1O__Type)
 : BWP_UplinkCommon__ext1O__F2 (BWP_UplinkCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_UplinkCommon__ext1O__F2F1_cond (y : seq_type BWP_UplinkCommon__ext1O__list)
  : seq_cond BWP_UplinkCommon__ext1O__list y ->
 (BWP_UplinkCommon__ext1O__cond (BWP_UplinkCommon__ext1O__F2 y)) /\  BWP_UplinkCommon__ext1O__F1 (BWP_UplinkCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_UplinkCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold BWP_UplinkCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_UplinkCommon__ext1O__Format : T_Format BWP_UplinkCommon__ext1O__Type BWP_UplinkCommon__ext1O__cond :=
        proj2_format  BWP_UplinkCommon__ext1O__cond BWP_UplinkCommon__ext1O__list__Format
    BWP_UplinkCommon__ext1O__F1 BWP_UplinkCommon__ext1O__F2 BWP_UplinkCommon__ext1O__F1F2_cond  BWP_UplinkCommon__ext1O__F1F2_cond2 BWP_UplinkCommon__ext1O__F2F1_cond.
Opaque BWP_UplinkCommon__ext1O__cond BWP_UplinkCommon__ext1O__Format.

Definition BWP_UplinkCommon__ext1__check_all_none (b : BWP_UplinkCommon__ext1O__Type) : bool :=
match b with 
  | make__BWP_UplinkCommon__ext1O__Type None None None None None  => false 
  | _ => true 
 end.
Definition BWP_UplinkCommon__ext1__Format : T_Format BWP_UplinkCommon__ext1__Type BWP_UplinkCommon__ext1__cond :=
  restrict_add_format BWP_UplinkCommon__ext1__check_all_none BWP_UplinkCommon__ext1O__Format.

Opaque BWP_UplinkCommon__ext1__cond BWP_UplinkCommon__ext1__Format.


Definition BWP_UplinkCommon__root_Format_Type := Eval cbn in seq_format_prod BWP_UplinkCommon__root_list.
Definition BWP_UplinkCommon__root_Format_list : BWP_UplinkCommon__root_Format_Type :=
  (BWP__Format, (BWP_UplinkCommon__rach_ConfigCommon__Format, (BWP_UplinkCommon__pusch_ConfigCommon__Format, (BWP_UplinkCommon__pucch_ConfigCommon__Format, unit_format)))).

Definition BWP_UplinkCommon__ext_Format_Type := Eval cbn in get_formats BWP_UplinkCommon__ext_list.
Definition BWP_UplinkCommon__ext_Format_list : BWP_UplinkCommon__ext_Format_Type :=
  (BWP_UplinkCommon__ext0__Format, (BWP_UplinkCommon__ext1__Format, unit__Format)).

Definition BWP_UplinkCommon__list_type : Set := (seq_type BWP_UplinkCommon__root_list) * (seq_ext_type BWP_UplinkCommon__ext_list).
Definition BWP_UplinkCommon__list_cond (z : BWP_UplinkCommon__list_type) : Prop :=
        (seq_cond BWP_UplinkCommon__root_list (fst z)) /\ (seq_ext_cond BWP_UplinkCommon__ext_list (snd z)).
Definition BWP_UplinkCommon__list_format : T_Format BWP_UplinkCommon__list_type BWP_UplinkCommon__list_cond :=
 (* Eval compute in *) seq_ext_format BWP_UplinkCommon__root_list BWP_UplinkCommon__root_Format_list BWP_UplinkCommon__ext_list BWP_UplinkCommon__ext_Format_list.

Opaque BWP_UplinkCommon__list_format.
Definition BWP_UplinkCommon__F1 (z : BWP_UplinkCommon__Type) : BWP_UplinkCommon__list_type :=
  (((BWP_UplinkCommon__genericParameters z, (BWP_UplinkCommon__rach_ConfigCommon z, (BWP_UplinkCommon__pusch_ConfigCommon z, (BWP_UplinkCommon__pucch_ConfigCommon z, tt))))), (
(BWP_UplinkCommon__ext0 z, (BWP_UplinkCommon__ext1 z, tt)))).
Definition BWP_UplinkCommon__F2 (y : BWP_UplinkCommon__list_type) : BWP_UplinkCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__BWP_UplinkCommon__Type j0 j1 j2 j3 i0 i1
  end.
Definition BWP_UplinkCommon__helper1 : (forall a : BWP_UplinkCommon__Type, BWP_UplinkCommon__cond a -> BWP_UplinkCommon__list_cond (BWP_UplinkCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BWP_UplinkCommon__helper2 : (forall a : BWP_UplinkCommon__Type, BWP_UplinkCommon__F2 (BWP_UplinkCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BWP_UplinkCommon__helper3 : (forall b : BWP_UplinkCommon__list_type, BWP_UplinkCommon__list_cond b -> BWP_UplinkCommon__cond (BWP_UplinkCommon__F2 b) /\ BWP_UplinkCommon__F1 (BWP_UplinkCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BWP_UplinkCommon__cond, BWP_UplinkCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BWP_UplinkCommon__Format : T_Format BWP_UplinkCommon__Type BWP_UplinkCommon__cond :=
 proj2_format BWP_UplinkCommon__cond BWP_UplinkCommon__list_format  BWP_UplinkCommon__F1 BWP_UplinkCommon__F2 BWP_UplinkCommon__helper1 BWP_UplinkCommon__helper2 BWP_UplinkCommon__helper3.

Opaque BWP_UplinkCommon__cond BWP_UplinkCommon__Format.

