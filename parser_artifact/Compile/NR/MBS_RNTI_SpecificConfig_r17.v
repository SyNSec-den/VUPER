Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MBS_RNTI_SpecificConfigId_r17.

Opaque MBS_RNTI_SpecificConfigId_r17__cond MBS_RNTI_SpecificConfigId_r17__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.


Inductive MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type : Set :=
  | MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g_RNTI : RNTI_Value__Type -> MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type
  | MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g_CS_RNTI : RNTI_Value__Type -> MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type
.
Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list : list typ := (
typ_cons RNTI_Value__Type RNTI_Value__cond ::
typ_cons RNTI_Value__Type RNTI_Value__cond ::
 nil).
Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__cond (c : MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type) := 
  match c with
  | MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g_RNTI t => RNTI_Value__cond t 
  | MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g_CS_RNTI t => RNTI_Value__cond t 
  end.

Lemma MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__len_helper1 : to_bit_sz (length MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__len_helper2 : 2 <= length2 MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list.
 simpl. lia. Qed.
Require Import NR.SetupRelease.
Require Import NR.DRX_ConfigPTM_r17.
Definition MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__Type := SetupRelease__Type DRX_ConfigPTM_r17__Type.
Definition MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__cond := SetupRelease__cond _ DRX_ConfigPTM_r17__cond.
Definition MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__Format : T_Format MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__Type MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__cond := SetupRelease__Format _ _ DRX_ConfigPTM_r17__Format.
Opaque MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__cond MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__Format.

Inductive MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Type : Set :=
 | MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__dci_enabler
 | MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__enabled
.
Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__cond := (fun (_ : MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Type) => True).
Lemma MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__nat__helper.

Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F1 t :=
  match t with
  | MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__dci_enabler => 0
  | MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__enabled => 1
  end.
Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F2 n :=
  match n with
  | 0 => MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__dci_enabler
  | 1 => MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__enabled
  | _ => MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__dci_enabler
  end.
Lemma MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F1F2 : forall x : MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Type, (MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F1 x <= 1) /\ MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F2 (MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F2F1 : forall (y : nat) (H : y <= 1), MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F1 (MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Type : Set :=
 | MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__ack_nack
 | MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__nack_only
.
Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__cond := (fun (_ : MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Type) => True).
Lemma MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__nat__helper.

Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F1 t :=
  match t with
  | MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__ack_nack => 0
  | MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__nack_only => 1
  end.
Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F2 n :=
  match n with
  | 0 => MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__ack_nack
  | 1 => MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__nack_only
  | _ => MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__ack_nack
  end.
Lemma MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F1F2 : forall x : MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Type, (MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F1 x <= 1) /\ MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F2 (MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F2F1 : forall (y : nat) (H : y <= 1), MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F1 (MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Type : Set :=
 | MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n2
 | MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n4
 | MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n8
.
Definition MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__cond := (fun (_ : MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Type) => True).
Lemma MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__nat__helper.

Definition MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F1 t :=
  match t with
  | MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n2 => 0
  | MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n4 => 1
  | MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n8 => 2
  end.
Definition MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F2 n :=
  match n with
  | 0 => MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n2
  | 1 => MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n4
  | 2 => MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n8
  | _ => MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__n2
  end.
Lemma MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F1F2 : forall x : MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Type, (MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F1 x <= 2) /\ MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F2 (MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F1 x) = x. imp_solve. Qed.
Lemma MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F2F1 : forall (y : nat) (H : y <= 2), MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F1 (MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F2 y) = y. enum_solve H y. Qed.

Record MBS_RNTI_SpecificConfig_r17__Type : Set :=
  make__MBS_RNTI_SpecificConfig_r17__Type {
    MBS_RNTI_SpecificConfig_r17__mbs_RNTI_SpecificConfigId_r17 : MBS_RNTI_SpecificConfigId_r17__Type ;
    MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17 : MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type ;
    MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17 : option MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__Type ;
    MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17 : option MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Type ;
    MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17 : option MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Type ;
    MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17 : option MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Type ;
}.
Definition MBS_RNTI_SpecificConfig_r17__list := (
 Nor MBS_RNTI_SpecificConfigId_r17__Type MBS_RNTI_SpecificConfigId_r17__cond ::
 Nor MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__cond ::
 Opt MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__Type MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__cond ::
 Opt MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Type MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__cond ::
 Opt MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Type MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__cond ::
 Opt MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Type MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__cond ::
 nil).
Definition MBS_RNTI_SpecificConfig_r17__cond z := 
  MBS_RNTI_SpecificConfigId_r17__cond (MBS_RNTI_SpecificConfig_r17__mbs_RNTI_SpecificConfigId_r17 z) /\
  MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__cond (MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17 z) /\
  opt_cond MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__cond (MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17 z) /\
  opt_cond MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__cond (MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17 z) /\
  opt_cond MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__cond (MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17 z) /\
  opt_cond MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__cond (MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17 z) /\
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

Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Format_Type := Eval cbn in get_formats MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list.
Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Format_list : MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Format_Type :=
  (RNTI_Value__Format, (RNTI_Value__Format, unit__Format)).
Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list__Format := Eval compute in choice_format MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__len_helper1 MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__len_helper2  MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Format_list.
Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F1 (z : MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type) : (choice MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list) :=
  match z with
   | MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g_RNTI t => existT _ 0 t
  | MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g_CS_RNTI t => existT _ 1 t
  end.
Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g := (fun n => typ_set (get_nth_typ MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list n)).
Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F2 (y : choice MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list) : MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g n -> MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type) with
    | 0 => fun (t : RNTI_Value__Type) => MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g_RNTI t 
    | 1 => fun (t : RNTI_Value__Type) => MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g_CS_RNTI t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type with end) n0
           end t0).

Lemma MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__helper2 :  forall (y : MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type), MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__cond y -> choice_cond MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list (MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__helper3 :  forall (y : MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type), MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F2 (MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__helper4 : (forall b : choice MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list, choice_cond MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list b -> MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__cond (MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F2 b) /\ MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F1 (MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F1 MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F2.
Definition MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Format : T_Format MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Type MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__cond :=
  (* Eval compute in *) proj2_format MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__cond MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__list__Format MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F1 MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__F2 MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__helper2 MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__helper3 MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__helper4.
Opaque MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__cond MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Format.

Opaque MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__cond MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__Format.

Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Format : T_Format MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__nat__Format MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F1 MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F2 MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F1F2 MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__F2F1.

Opaque MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__cond MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Format.

Definition MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Format : T_Format MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__nat__Format MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F1 MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F2 MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F1F2 MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__F2F1.

Opaque MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__cond MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Format.

Definition MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Format : T_Format MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__nat__Format MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F1 MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F2 MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F1F2 MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__F2F1.

Opaque MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__cond MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Format.


Definition MBS_RNTI_SpecificConfig_r17__Format_Type := Eval cbn in seq_format_prod MBS_RNTI_SpecificConfig_r17__list.
Definition MBS_RNTI_SpecificConfig_r17__Format_list : MBS_RNTI_SpecificConfig_r17__Format_Type :=
  (MBS_RNTI_SpecificConfigId_r17__Format, (MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17__Format, (MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17__Format, (MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17__Format, (MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17__Format, (MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17__Format, unit_format)))))).
Definition MBS_RNTI_SpecificConfig_r17__list__Format := (*Eval compute in *) seq_format MBS_RNTI_SpecificConfig_r17__list MBS_RNTI_SpecificConfig_r17__Format_list.
Definition MBS_RNTI_SpecificConfig_r17__F1 z :=
  (MBS_RNTI_SpecificConfig_r17__mbs_RNTI_SpecificConfigId_r17 z, (MBS_RNTI_SpecificConfig_r17__groupCommon_RNTI_r17 z, (MBS_RNTI_SpecificConfig_r17__drx_ConfigPTM_r17 z, (MBS_RNTI_SpecificConfig_r17__harq_FeedbackEnablerMulticast_r17 z, (MBS_RNTI_SpecificConfig_r17__harq_FeedbackOptionMulticast_r17 z, (MBS_RNTI_SpecificConfig_r17__pdsch_AggregationFactor_r17 z, tt)))))).
Definition MBS_RNTI_SpecificConfig_r17__F2 (y : seq_type MBS_RNTI_SpecificConfig_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__MBS_RNTI_SpecificConfig_r17__Type i0 i1 i2 i3 i4 i5
  end.
Lemma MBS_RNTI_SpecificConfig_r17__F1F2_cond (z : MBS_RNTI_SpecificConfig_r17__Type)
  : MBS_RNTI_SpecificConfig_r17__cond z ->
  (seq_cond MBS_RNTI_SpecificConfig_r17__list (MBS_RNTI_SpecificConfig_r17__F1 z)).
intro H. unfold MBS_RNTI_SpecificConfig_r17__cond in H. simpl. auto. Qed.
Lemma MBS_RNTI_SpecificConfig_r17__F1F2_cond2 (z : MBS_RNTI_SpecificConfig_r17__Type)
 : MBS_RNTI_SpecificConfig_r17__F2 (MBS_RNTI_SpecificConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MBS_RNTI_SpecificConfig_r17__F2F1_cond (y : seq_type MBS_RNTI_SpecificConfig_r17__list)
  : seq_cond MBS_RNTI_SpecificConfig_r17__list y ->
 (MBS_RNTI_SpecificConfig_r17__cond (MBS_RNTI_SpecificConfig_r17__F2 y)) /\  MBS_RNTI_SpecificConfig_r17__F1 (MBS_RNTI_SpecificConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MBS_RNTI_SpecificConfig_r17__cond. simpl in *. auto.
 - simpl. unfold MBS_RNTI_SpecificConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MBS_RNTI_SpecificConfig_r17__Format : T_Format MBS_RNTI_SpecificConfig_r17__Type MBS_RNTI_SpecificConfig_r17__cond :=
        proj2_format  MBS_RNTI_SpecificConfig_r17__cond MBS_RNTI_SpecificConfig_r17__list__Format
    MBS_RNTI_SpecificConfig_r17__F1 MBS_RNTI_SpecificConfig_r17__F2 MBS_RNTI_SpecificConfig_r17__F1F2_cond  MBS_RNTI_SpecificConfig_r17__F1F2_cond2 MBS_RNTI_SpecificConfig_r17__F2F1_cond.
Opaque MBS_RNTI_SpecificConfig_r17__cond MBS_RNTI_SpecificConfig_r17__Format.

