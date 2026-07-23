Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UL_GapFR2_Preference_r17.

Opaque UL_GapFR2_Preference_r17__cond UL_GapFR2_Preference_r17__Format.

Require Import NR.MUSIM_Assistance_r17.

Opaque MUSIM_Assistance_r17__cond MUSIM_Assistance_r17__Format.

Require Import NR.OverheatingAssistance_r17.

Opaque OverheatingAssistance_r17__cond OverheatingAssistance_r17__Format.

Require Import NR.MaxBW_PreferenceFR2_2_r17.

Opaque MaxBW_PreferenceFR2_2_r17__cond MaxBW_PreferenceFR2_2_r17__Format.

Require Import NR.MaxMIMO_LayerPreferenceFR2_2_r17.

Opaque MaxMIMO_LayerPreferenceFR2_2_r17__cond MaxMIMO_LayerPreferenceFR2_2_r17__Format.

Require Import NR.MinSchedulingOffsetPreferenceExt_r17.

Opaque MinSchedulingOffsetPreferenceExt_r17__cond MinSchedulingOffsetPreferenceExt_r17__Format.

Lemma UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Type := bit_string.
Definition UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= maxNrofServingCells)%Z /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.ResumeCause.

Opaque ResumeCause__cond ResumeCause__Format.

Record UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type : Set :=
  make__UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type {
    UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__resumeCause_r17 : option ResumeCause__Type ;
}.
Definition UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list := (
 Opt ResumeCause__Type ResumeCause__cond ::
 nil).
Definition UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond z := 
  opt_cond ResumeCause__cond (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__resumeCause_r17 z) /\
  True.

Inductive UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type : Set :=
 | UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__scgDeactivationPreferred
 | UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__noPreference
.
Definition UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__cond := (fun (_ : UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type) => True).
Lemma UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__nat__helper.

Definition UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F1 t :=
  match t with
  | UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__scgDeactivationPreferred => 0
  | UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__noPreference => 1
  end.
Definition UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F2 n :=
  match n with
  | 0 => UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__scgDeactivationPreferred
  | 1 => UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__noPreference
  | _ => UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__scgDeactivationPreferred
  end.
Lemma UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F1F2 : forall x : UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type, (UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F1 x <= 1) /\ UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F2 (UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F1 x) = x. imp_solve. Qed.
Lemma UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F2F1 : forall (y : nat) (H : y <= 1), UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F1 (UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UEAssistanceInformation_v1700_IEs__uplinkData_r17__Type : Set :=
 | UEAssistanceInformation_v1700_IEs__uplinkData_r17__true
.
Definition UEAssistanceInformation_v1700_IEs__uplinkData_r17__cond := (fun (_ : UEAssistanceInformation_v1700_IEs__uplinkData_r17__Type) => True).
Lemma UEAssistanceInformation_v1700_IEs__uplinkData_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEAssistanceInformation_v1700_IEs__uplinkData_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEAssistanceInformation_v1700_IEs__uplinkData_r17__nat__helper.

Definition UEAssistanceInformation_v1700_IEs__uplinkData_r17__F1 t :=
  match t with
  | UEAssistanceInformation_v1700_IEs__uplinkData_r17__true => 0
  end.
Definition UEAssistanceInformation_v1700_IEs__uplinkData_r17__F2 n :=
  match n with
  | 0 => UEAssistanceInformation_v1700_IEs__uplinkData_r17__true
  | _ => UEAssistanceInformation_v1700_IEs__uplinkData_r17__true
  end.
Lemma UEAssistanceInformation_v1700_IEs__uplinkData_r17__F1F2 : forall x : UEAssistanceInformation_v1700_IEs__uplinkData_r17__Type, (UEAssistanceInformation_v1700_IEs__uplinkData_r17__F1 x <= 0) /\ UEAssistanceInformation_v1700_IEs__uplinkData_r17__F2 (UEAssistanceInformation_v1700_IEs__uplinkData_r17__F1 x) = x. imp_solve. Qed.
Lemma UEAssistanceInformation_v1700_IEs__uplinkData_r17__F2F1 : forall (y : nat) (H : y <= 0), UEAssistanceInformation_v1700_IEs__uplinkData_r17__F1 (UEAssistanceInformation_v1700_IEs__uplinkData_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PropagationDelayDifference_r17.

Opaque PropagationDelayDifference_r17__cond PropagationDelayDifference_r17__Format.

Record UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type : Set := make__UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type {}.
Definition UEAssistanceInformation_v1700_IEs__nonCriticalExtension__cond (z : UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type) := True.
Record UEAssistanceInformation_v1700_IEs__Type : Set :=
  make__UEAssistanceInformation_v1700_IEs__Type {
    UEAssistanceInformation_v1700_IEs__ul_GapFR2_Preference_r17 : option UL_GapFR2_Preference_r17__Type ;
    UEAssistanceInformation_v1700_IEs__musim_Assistance_r17 : option MUSIM_Assistance_r17__Type ;
    UEAssistanceInformation_v1700_IEs__overheatingAssistance_r17 : option OverheatingAssistance_r17__Type ;
    UEAssistanceInformation_v1700_IEs__maxBW_PreferenceFR2_2_r17 : option MaxBW_PreferenceFR2_2_r17__Type ;
    UEAssistanceInformation_v1700_IEs__maxMIMO_LayerPreferenceFR2_2_r17 : option MaxMIMO_LayerPreferenceFR2_2_r17__Type ;
    UEAssistanceInformation_v1700_IEs__minSchedulingOffsetPreferenceExt_r17 : option MinSchedulingOffsetPreferenceExt_r17__Type ;
    UEAssistanceInformation_v1700_IEs__rlm_MeasRelaxationState_r17 : option bool ;
    UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17 : option UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Type ;
    UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17 : option UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type ;
    UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17 : option UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type ;
    UEAssistanceInformation_v1700_IEs__uplinkData_r17 : option UEAssistanceInformation_v1700_IEs__uplinkData_r17__Type ;
    UEAssistanceInformation_v1700_IEs__rrm_MeasRelaxationFulfilment_r17 : option bool ;
    UEAssistanceInformation_v1700_IEs__propagationDelayDifference_r17 : option PropagationDelayDifference_r17__Type ;
    UEAssistanceInformation_v1700_IEs__nonCriticalExtension : option UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition UEAssistanceInformation_v1700_IEs__list := (
 Opt UL_GapFR2_Preference_r17__Type UL_GapFR2_Preference_r17__cond ::
 Opt MUSIM_Assistance_r17__Type MUSIM_Assistance_r17__cond ::
 Opt OverheatingAssistance_r17__Type OverheatingAssistance_r17__cond ::
 Opt MaxBW_PreferenceFR2_2_r17__Type MaxBW_PreferenceFR2_2_r17__cond ::
 Opt MaxMIMO_LayerPreferenceFR2_2_r17__Type MaxMIMO_LayerPreferenceFR2_2_r17__cond ::
 Opt MinSchedulingOffsetPreferenceExt_r17__Type MinSchedulingOffsetPreferenceExt_r17__cond ::
 Opt bool (fun _ => True) ::
 Opt UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Type UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__cond ::
 Opt UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond ::
 Opt UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__cond ::
 Opt UEAssistanceInformation_v1700_IEs__uplinkData_r17__Type UEAssistanceInformation_v1700_IEs__uplinkData_r17__cond ::
 Opt bool (fun _ => True) ::
 Opt PropagationDelayDifference_r17__Type PropagationDelayDifference_r17__cond ::
 Opt UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type UEAssistanceInformation_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition UEAssistanceInformation_v1700_IEs__cond z := 
  opt_cond UL_GapFR2_Preference_r17__cond (UEAssistanceInformation_v1700_IEs__ul_GapFR2_Preference_r17 z) /\
  opt_cond MUSIM_Assistance_r17__cond (UEAssistanceInformation_v1700_IEs__musim_Assistance_r17 z) /\
  opt_cond OverheatingAssistance_r17__cond (UEAssistanceInformation_v1700_IEs__overheatingAssistance_r17 z) /\
  opt_cond MaxBW_PreferenceFR2_2_r17__cond (UEAssistanceInformation_v1700_IEs__maxBW_PreferenceFR2_2_r17 z) /\
  opt_cond MaxMIMO_LayerPreferenceFR2_2_r17__cond (UEAssistanceInformation_v1700_IEs__maxMIMO_LayerPreferenceFR2_2_r17 z) /\
  opt_cond MinSchedulingOffsetPreferenceExt_r17__cond (UEAssistanceInformation_v1700_IEs__minSchedulingOffsetPreferenceExt_r17 z) /\
  opt_cond (fun _ => True) (UEAssistanceInformation_v1700_IEs__rlm_MeasRelaxationState_r17 z) /\
  opt_cond UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__cond (UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17 z) /\
  opt_cond UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17 z) /\
  opt_cond UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__cond (UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17 z) /\
  opt_cond UEAssistanceInformation_v1700_IEs__uplinkData_r17__cond (UEAssistanceInformation_v1700_IEs__uplinkData_r17 z) /\
  opt_cond (fun _ => True) (UEAssistanceInformation_v1700_IEs__rrm_MeasRelaxationFulfilment_r17 z) /\
  opt_cond PropagationDelayDifference_r17__cond (UEAssistanceInformation_v1700_IEs__propagationDelayDifference_r17 z) /\
  opt_cond UEAssistanceInformation_v1700_IEs__nonCriticalExtension__cond (UEAssistanceInformation_v1700_IEs__nonCriticalExtension z) /\
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
Definition UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Format : T_Format UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Type UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 maxNrofServingCells UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__helper1 UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__helper2.
Opaque UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__cond UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Format.


Definition UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format_Type := Eval cbn in seq_format_prod UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list.
Definition UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format_list : UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format_Type :=
  (ResumeCause__Format, unit_format).
Definition UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list__Format := (*Eval compute in *) seq_format UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format_list.
Definition UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1 z :=
  (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__resumeCause_r17 z, tt).
Definition UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F2 (y : seq_type UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list) :=
  match y with
  | (i0, _)=>
    make__UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type i0
  end.
Lemma UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1F2_cond (z : UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type)
  : UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond z ->
  (seq_cond UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1 z)).
intro H. unfold UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond in H. simpl. auto. Qed.
Lemma UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1F2_cond2 (z : UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type)
 : UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F2 (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F2F1_cond (y : seq_type UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list)
  : seq_cond UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list y ->
 (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F2 y)) /\  UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1 (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond. simpl in *. auto.
 - simpl. unfold UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format : T_Format UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Type UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond :=
        proj2_format  UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__list__Format
    UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1 UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F2 UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1F2_cond  UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F1F2_cond2 UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__F2F1_cond.
Opaque UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__cond UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format.

Definition UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Format : T_Format UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__nat__Format UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F1 UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F2 UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F1F2 UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__F2F1.

Opaque UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__cond UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Format.

Definition UEAssistanceInformation_v1700_IEs__uplinkData_r17__Format : T_Format UEAssistanceInformation_v1700_IEs__uplinkData_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEAssistanceInformation_v1700_IEs__uplinkData_r17__nat__Format UEAssistanceInformation_v1700_IEs__uplinkData_r17__F1 UEAssistanceInformation_v1700_IEs__uplinkData_r17__F2 UEAssistanceInformation_v1700_IEs__uplinkData_r17__F1F2 UEAssistanceInformation_v1700_IEs__uplinkData_r17__F2F1.

Opaque UEAssistanceInformation_v1700_IEs__uplinkData_r17__cond UEAssistanceInformation_v1700_IEs__uplinkData_r17__Format.

Definition UEAssistanceInformation_v1700_IEs__nonCriticalExtension__helper : forall a : UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Format : T_Format UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type UEAssistanceInformation_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Type)
    UEAssistanceInformation_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque UEAssistanceInformation_v1700_IEs__nonCriticalExtension__cond UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Format.


Definition UEAssistanceInformation_v1700_IEs__Format_Type := Eval cbn in seq_format_prod UEAssistanceInformation_v1700_IEs__list.
Definition UEAssistanceInformation_v1700_IEs__Format_list : UEAssistanceInformation_v1700_IEs__Format_Type :=
  (UL_GapFR2_Preference_r17__Format, (MUSIM_Assistance_r17__Format, (OverheatingAssistance_r17__Format, (MaxBW_PreferenceFR2_2_r17__Format, (MaxMIMO_LayerPreferenceFR2_2_r17__Format, (MinSchedulingOffsetPreferenceExt_r17__Format, (bool__Format, (UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17__Format, (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17__Format, (UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17__Format, (UEAssistanceInformation_v1700_IEs__uplinkData_r17__Format, (bool__Format, (PropagationDelayDifference_r17__Format, (UEAssistanceInformation_v1700_IEs__nonCriticalExtension__Format, unit_format)))))))))))))).
Definition UEAssistanceInformation_v1700_IEs__list__Format := (*Eval compute in *) seq_format UEAssistanceInformation_v1700_IEs__list UEAssistanceInformation_v1700_IEs__Format_list.
Definition UEAssistanceInformation_v1700_IEs__F1 z :=
  (UEAssistanceInformation_v1700_IEs__ul_GapFR2_Preference_r17 z, (UEAssistanceInformation_v1700_IEs__musim_Assistance_r17 z, (UEAssistanceInformation_v1700_IEs__overheatingAssistance_r17 z, (UEAssistanceInformation_v1700_IEs__maxBW_PreferenceFR2_2_r17 z, (UEAssistanceInformation_v1700_IEs__maxMIMO_LayerPreferenceFR2_2_r17 z, (UEAssistanceInformation_v1700_IEs__minSchedulingOffsetPreferenceExt_r17 z, (UEAssistanceInformation_v1700_IEs__rlm_MeasRelaxationState_r17 z, (UEAssistanceInformation_v1700_IEs__bfd_MeasRelaxationState_r17 z, (UEAssistanceInformation_v1700_IEs__nonSDT_DataIndication_r17 z, (UEAssistanceInformation_v1700_IEs__scg_DeactivationPreference_r17 z, (UEAssistanceInformation_v1700_IEs__uplinkData_r17 z, (UEAssistanceInformation_v1700_IEs__rrm_MeasRelaxationFulfilment_r17 z, (UEAssistanceInformation_v1700_IEs__propagationDelayDifference_r17 z, (UEAssistanceInformation_v1700_IEs__nonCriticalExtension z, tt)))))))))))))).
Definition UEAssistanceInformation_v1700_IEs__F2 (y : seq_type UEAssistanceInformation_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, _))))))))))))))=>
    make__UEAssistanceInformation_v1700_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  end.
Lemma UEAssistanceInformation_v1700_IEs__F1F2_cond (z : UEAssistanceInformation_v1700_IEs__Type)
  : UEAssistanceInformation_v1700_IEs__cond z ->
  (seq_cond UEAssistanceInformation_v1700_IEs__list (UEAssistanceInformation_v1700_IEs__F1 z)).
intro H. unfold UEAssistanceInformation_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma UEAssistanceInformation_v1700_IEs__F1F2_cond2 (z : UEAssistanceInformation_v1700_IEs__Type)
 : UEAssistanceInformation_v1700_IEs__F2 (UEAssistanceInformation_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEAssistanceInformation_v1700_IEs__F2F1_cond (y : seq_type UEAssistanceInformation_v1700_IEs__list)
  : seq_cond UEAssistanceInformation_v1700_IEs__list y ->
 (UEAssistanceInformation_v1700_IEs__cond (UEAssistanceInformation_v1700_IEs__F2 y)) /\  UEAssistanceInformation_v1700_IEs__F1 (UEAssistanceInformation_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEAssistanceInformation_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold UEAssistanceInformation_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEAssistanceInformation_v1700_IEs__Format : T_Format UEAssistanceInformation_v1700_IEs__Type UEAssistanceInformation_v1700_IEs__cond :=
        proj2_format  UEAssistanceInformation_v1700_IEs__cond UEAssistanceInformation_v1700_IEs__list__Format
    UEAssistanceInformation_v1700_IEs__F1 UEAssistanceInformation_v1700_IEs__F2 UEAssistanceInformation_v1700_IEs__F1F2_cond  UEAssistanceInformation_v1700_IEs__F1F2_cond2 UEAssistanceInformation_v1700_IEs__F2F1_cond.
Opaque UEAssistanceInformation_v1700_IEs__cond UEAssistanceInformation_v1700_IEs__Format.

