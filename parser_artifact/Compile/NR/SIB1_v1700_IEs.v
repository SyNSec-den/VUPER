Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SIB1_v1700_IEs__hsdn_Cell_r17__Type : Set :=
 | SIB1_v1700_IEs__hsdn_Cell_r17__true
.
Definition SIB1_v1700_IEs__hsdn_Cell_r17__cond := (fun (_ : SIB1_v1700_IEs__hsdn_Cell_r17__Type) => True).
Lemma SIB1_v1700_IEs__hsdn_Cell_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1_v1700_IEs__hsdn_Cell_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB1_v1700_IEs__hsdn_Cell_r17__nat__helper.

Definition SIB1_v1700_IEs__hsdn_Cell_r17__F1 t :=
  match t with
  | SIB1_v1700_IEs__hsdn_Cell_r17__true => 0
  end.
Definition SIB1_v1700_IEs__hsdn_Cell_r17__F2 n :=
  match n with
  | 0 => SIB1_v1700_IEs__hsdn_Cell_r17__true
  | _ => SIB1_v1700_IEs__hsdn_Cell_r17__true
  end.
Lemma SIB1_v1700_IEs__hsdn_Cell_r17__F1F2 : forall x : SIB1_v1700_IEs__hsdn_Cell_r17__Type, (SIB1_v1700_IEs__hsdn_Cell_r17__F1 x <= 0) /\ SIB1_v1700_IEs__hsdn_Cell_r17__F2 (SIB1_v1700_IEs__hsdn_Cell_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB1_v1700_IEs__hsdn_Cell_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB1_v1700_IEs__hsdn_Cell_r17__F1 (SIB1_v1700_IEs__hsdn_Cell_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UAC_BarringInfoSetList_v1700.

Opaque UAC_BarringInfoSetList_v1700__cond UAC_BarringInfoSetList_v1700__Format.

Record SIB1_v1700_IEs__uac_BarringInfo_v1700__Type : Set :=
  make__SIB1_v1700_IEs__uac_BarringInfo_v1700__Type {
    SIB1_v1700_IEs__uac_BarringInfo_v1700__uac_BarringInfoSetList_v1700 : UAC_BarringInfoSetList_v1700__Type ;
}.
Definition SIB1_v1700_IEs__uac_BarringInfo_v1700__list := (
 Nor UAC_BarringInfoSetList_v1700__Type UAC_BarringInfoSetList_v1700__cond ::
 nil).
Definition SIB1_v1700_IEs__uac_BarringInfo_v1700__cond z := 
  UAC_BarringInfoSetList_v1700__cond (SIB1_v1700_IEs__uac_BarringInfo_v1700__uac_BarringInfoSetList_v1700 z) /\
  True.

Require Import NR.SDT_ConfigCommonSIB_r17.

Opaque SDT_ConfigCommonSIB_r17__cond SDT_ConfigCommonSIB_r17__Format.

Require Import NR.RedCap_ConfigCommonSIB_r17.

Opaque RedCap_ConfigCommonSIB_r17__cond RedCap_ConfigCommonSIB_r17__Format.

Require Import NR.FeaturePriority_r17.

Opaque FeaturePriority_r17__cond FeaturePriority_r17__Format.

Require Import NR.FeaturePriority_r17.

Opaque FeaturePriority_r17__cond FeaturePriority_r17__Format.

Require Import NR.FeaturePriority_r17.

Opaque FeaturePriority_r17__cond FeaturePriority_r17__Format.

Require Import NR.FeaturePriority_r17.

Opaque FeaturePriority_r17__cond FeaturePriority_r17__Format.

Record SIB1_v1700_IEs__featurePriorities_r17__Type : Set :=
  make__SIB1_v1700_IEs__featurePriorities_r17__Type {
    SIB1_v1700_IEs__featurePriorities_r17__redCapPriority_r17 : option FeaturePriority_r17__Type ;
    SIB1_v1700_IEs__featurePriorities_r17__slicingPriority_r17 : option FeaturePriority_r17__Type ;
    SIB1_v1700_IEs__featurePriorities_r17__msg3_Repetitions_Priority_r17 : option FeaturePriority_r17__Type ;
    SIB1_v1700_IEs__featurePriorities_r17__sdt_Priority_r17 : option FeaturePriority_r17__Type ;
}.
Definition SIB1_v1700_IEs__featurePriorities_r17__list := (
 Opt FeaturePriority_r17__Type FeaturePriority_r17__cond ::
 Opt FeaturePriority_r17__Type FeaturePriority_r17__cond ::
 Opt FeaturePriority_r17__Type FeaturePriority_r17__cond ::
 Opt FeaturePriority_r17__Type FeaturePriority_r17__cond ::
 nil).
Definition SIB1_v1700_IEs__featurePriorities_r17__cond z := 
  opt_cond FeaturePriority_r17__cond (SIB1_v1700_IEs__featurePriorities_r17__redCapPriority_r17 z) /\
  opt_cond FeaturePriority_r17__cond (SIB1_v1700_IEs__featurePriorities_r17__slicingPriority_r17 z) /\
  opt_cond FeaturePriority_r17__cond (SIB1_v1700_IEs__featurePriorities_r17__msg3_Repetitions_Priority_r17 z) /\
  opt_cond FeaturePriority_r17__cond (SIB1_v1700_IEs__featurePriorities_r17__sdt_Priority_r17 z) /\
  True.

Require Import NR.SI_SchedulingInfo_v1700.

Opaque SI_SchedulingInfo_v1700__cond SI_SchedulingInfo_v1700__Format.

Definition SIB1_v1700_IEs__hyperSFN_r17__Type := bit_string_fixed.
Definition SIB1_v1700_IEs__hyperSFN_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Inductive SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Type : Set :=
 | SIB1_v1700_IEs__eDRX_AllowedIdle_r17__true
.
Definition SIB1_v1700_IEs__eDRX_AllowedIdle_r17__cond := (fun (_ : SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Type) => True).
Lemma SIB1_v1700_IEs__eDRX_AllowedIdle_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1_v1700_IEs__eDRX_AllowedIdle_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB1_v1700_IEs__eDRX_AllowedIdle_r17__nat__helper.

Definition SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F1 t :=
  match t with
  | SIB1_v1700_IEs__eDRX_AllowedIdle_r17__true => 0
  end.
Definition SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F2 n :=
  match n with
  | 0 => SIB1_v1700_IEs__eDRX_AllowedIdle_r17__true
  | _ => SIB1_v1700_IEs__eDRX_AllowedIdle_r17__true
  end.
Lemma SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F1F2 : forall x : SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Type, (SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F1 x <= 0) /\ SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F2 (SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F1 (SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Type : Set :=
 | SIB1_v1700_IEs__eDRX_AllowedInactive_r17__true
.
Definition SIB1_v1700_IEs__eDRX_AllowedInactive_r17__cond := (fun (_ : SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Type) => True).
Lemma SIB1_v1700_IEs__eDRX_AllowedInactive_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1_v1700_IEs__eDRX_AllowedInactive_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB1_v1700_IEs__eDRX_AllowedInactive_r17__nat__helper.

Definition SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F1 t :=
  match t with
  | SIB1_v1700_IEs__eDRX_AllowedInactive_r17__true => 0
  end.
Definition SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F2 n :=
  match n with
  | 0 => SIB1_v1700_IEs__eDRX_AllowedInactive_r17__true
  | _ => SIB1_v1700_IEs__eDRX_AllowedInactive_r17__true
  end.
Lemma SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F1F2 : forall x : SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Type, (SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F1 x <= 0) /\ SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F2 (SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F1 (SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Type : Set :=
 | SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__allowed
 | SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__notAllowed
.
Definition SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__cond := (fun (_ : SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Type) => True).
Lemma SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__nat__helper.

Definition SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F1 t :=
  match t with
  | SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__allowed => 0
  | SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__notAllowed => 1
  end.
Definition SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F2 n :=
  match n with
  | 0 => SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__allowed
  | 1 => SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__notAllowed
  | _ => SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__allowed
  end.
Lemma SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F1F2 : forall x : SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Type, (SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F1 x <= 1) /\ SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F2 (SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F2F1 : forall (y : nat) (H : y <= 1), SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F1 (SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SIB1_v1700_IEs__cellBarredNTN_r17__Type : Set :=
 | SIB1_v1700_IEs__cellBarredNTN_r17__barred
 | SIB1_v1700_IEs__cellBarredNTN_r17__notBarred
.
Definition SIB1_v1700_IEs__cellBarredNTN_r17__cond := (fun (_ : SIB1_v1700_IEs__cellBarredNTN_r17__Type) => True).
Lemma SIB1_v1700_IEs__cellBarredNTN_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1_v1700_IEs__cellBarredNTN_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SIB1_v1700_IEs__cellBarredNTN_r17__nat__helper.

Definition SIB1_v1700_IEs__cellBarredNTN_r17__F1 t :=
  match t with
  | SIB1_v1700_IEs__cellBarredNTN_r17__barred => 0
  | SIB1_v1700_IEs__cellBarredNTN_r17__notBarred => 1
  end.
Definition SIB1_v1700_IEs__cellBarredNTN_r17__F2 n :=
  match n with
  | 0 => SIB1_v1700_IEs__cellBarredNTN_r17__barred
  | 1 => SIB1_v1700_IEs__cellBarredNTN_r17__notBarred
  | _ => SIB1_v1700_IEs__cellBarredNTN_r17__barred
  end.
Lemma SIB1_v1700_IEs__cellBarredNTN_r17__F1F2 : forall x : SIB1_v1700_IEs__cellBarredNTN_r17__Type, (SIB1_v1700_IEs__cellBarredNTN_r17__F1 x <= 1) /\ SIB1_v1700_IEs__cellBarredNTN_r17__F2 (SIB1_v1700_IEs__cellBarredNTN_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB1_v1700_IEs__cellBarredNTN_r17__F2F1 : forall (y : nat) (H : y <= 1), SIB1_v1700_IEs__cellBarredNTN_r17__F1 (SIB1_v1700_IEs__cellBarredNTN_r17__F2 y) = y. enum_solve H y. Qed.

Record SIB1_v1700_IEs__nonCriticalExtension__Type : Set := make__SIB1_v1700_IEs__nonCriticalExtension__Type {}.
Definition SIB1_v1700_IEs__nonCriticalExtension__cond (z : SIB1_v1700_IEs__nonCriticalExtension__Type) := True.
Record SIB1_v1700_IEs__Type : Set :=
  make__SIB1_v1700_IEs__Type {
    SIB1_v1700_IEs__hsdn_Cell_r17 : option SIB1_v1700_IEs__hsdn_Cell_r17__Type ;
    SIB1_v1700_IEs__uac_BarringInfo_v1700 : option SIB1_v1700_IEs__uac_BarringInfo_v1700__Type ;
    SIB1_v1700_IEs__sdt_ConfigCommon_r17 : option SDT_ConfigCommonSIB_r17__Type ;
    SIB1_v1700_IEs__redCap_ConfigCommon_r17 : option RedCap_ConfigCommonSIB_r17__Type ;
    SIB1_v1700_IEs__featurePriorities_r17 : option SIB1_v1700_IEs__featurePriorities_r17__Type ;
    SIB1_v1700_IEs__si_SchedulingInfo_v1700 : option SI_SchedulingInfo_v1700__Type ;
    SIB1_v1700_IEs__hyperSFN_r17 : option SIB1_v1700_IEs__hyperSFN_r17__Type ;
    SIB1_v1700_IEs__eDRX_AllowedIdle_r17 : option SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Type ;
    SIB1_v1700_IEs__eDRX_AllowedInactive_r17 : option SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Type ;
    SIB1_v1700_IEs__intraFreqReselectionRedCap_r17 : option SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Type ;
    SIB1_v1700_IEs__cellBarredNTN_r17 : option SIB1_v1700_IEs__cellBarredNTN_r17__Type ;
    SIB1_v1700_IEs__nonCriticalExtension : option SIB1_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition SIB1_v1700_IEs__list := (
 Opt SIB1_v1700_IEs__hsdn_Cell_r17__Type SIB1_v1700_IEs__hsdn_Cell_r17__cond ::
 Opt SIB1_v1700_IEs__uac_BarringInfo_v1700__Type SIB1_v1700_IEs__uac_BarringInfo_v1700__cond ::
 Opt SDT_ConfigCommonSIB_r17__Type SDT_ConfigCommonSIB_r17__cond ::
 Opt RedCap_ConfigCommonSIB_r17__Type RedCap_ConfigCommonSIB_r17__cond ::
 Opt SIB1_v1700_IEs__featurePriorities_r17__Type SIB1_v1700_IEs__featurePriorities_r17__cond ::
 Opt SI_SchedulingInfo_v1700__Type SI_SchedulingInfo_v1700__cond ::
 Opt SIB1_v1700_IEs__hyperSFN_r17__Type SIB1_v1700_IEs__hyperSFN_r17__cond ::
 Opt SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Type SIB1_v1700_IEs__eDRX_AllowedIdle_r17__cond ::
 Opt SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Type SIB1_v1700_IEs__eDRX_AllowedInactive_r17__cond ::
 Opt SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Type SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__cond ::
 Opt SIB1_v1700_IEs__cellBarredNTN_r17__Type SIB1_v1700_IEs__cellBarredNTN_r17__cond ::
 Opt SIB1_v1700_IEs__nonCriticalExtension__Type SIB1_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition SIB1_v1700_IEs__cond z := 
  opt_cond SIB1_v1700_IEs__hsdn_Cell_r17__cond (SIB1_v1700_IEs__hsdn_Cell_r17 z) /\
  opt_cond SIB1_v1700_IEs__uac_BarringInfo_v1700__cond (SIB1_v1700_IEs__uac_BarringInfo_v1700 z) /\
  opt_cond SDT_ConfigCommonSIB_r17__cond (SIB1_v1700_IEs__sdt_ConfigCommon_r17 z) /\
  opt_cond RedCap_ConfigCommonSIB_r17__cond (SIB1_v1700_IEs__redCap_ConfigCommon_r17 z) /\
  opt_cond SIB1_v1700_IEs__featurePriorities_r17__cond (SIB1_v1700_IEs__featurePriorities_r17 z) /\
  opt_cond SI_SchedulingInfo_v1700__cond (SIB1_v1700_IEs__si_SchedulingInfo_v1700 z) /\
  opt_cond SIB1_v1700_IEs__hyperSFN_r17__cond (SIB1_v1700_IEs__hyperSFN_r17 z) /\
  opt_cond SIB1_v1700_IEs__eDRX_AllowedIdle_r17__cond (SIB1_v1700_IEs__eDRX_AllowedIdle_r17 z) /\
  opt_cond SIB1_v1700_IEs__eDRX_AllowedInactive_r17__cond (SIB1_v1700_IEs__eDRX_AllowedInactive_r17 z) /\
  opt_cond SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__cond (SIB1_v1700_IEs__intraFreqReselectionRedCap_r17 z) /\
  opt_cond SIB1_v1700_IEs__cellBarredNTN_r17__cond (SIB1_v1700_IEs__cellBarredNTN_r17 z) /\
  opt_cond SIB1_v1700_IEs__nonCriticalExtension__cond (SIB1_v1700_IEs__nonCriticalExtension z) /\
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
Definition SIB1_v1700_IEs__hsdn_Cell_r17__Format : T_Format SIB1_v1700_IEs__hsdn_Cell_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1_v1700_IEs__hsdn_Cell_r17__nat__Format SIB1_v1700_IEs__hsdn_Cell_r17__F1 SIB1_v1700_IEs__hsdn_Cell_r17__F2 SIB1_v1700_IEs__hsdn_Cell_r17__F1F2 SIB1_v1700_IEs__hsdn_Cell_r17__F2F1.

Opaque SIB1_v1700_IEs__hsdn_Cell_r17__cond SIB1_v1700_IEs__hsdn_Cell_r17__Format.


Definition SIB1_v1700_IEs__uac_BarringInfo_v1700__Format_Type := Eval cbn in seq_format_prod SIB1_v1700_IEs__uac_BarringInfo_v1700__list.
Definition SIB1_v1700_IEs__uac_BarringInfo_v1700__Format_list : SIB1_v1700_IEs__uac_BarringInfo_v1700__Format_Type :=
  (UAC_BarringInfoSetList_v1700__Format, unit_format).
Definition SIB1_v1700_IEs__uac_BarringInfo_v1700__list__Format := (*Eval compute in *) seq_format SIB1_v1700_IEs__uac_BarringInfo_v1700__list SIB1_v1700_IEs__uac_BarringInfo_v1700__Format_list.
Definition SIB1_v1700_IEs__uac_BarringInfo_v1700__F1 z :=
  (SIB1_v1700_IEs__uac_BarringInfo_v1700__uac_BarringInfoSetList_v1700 z, tt).
Definition SIB1_v1700_IEs__uac_BarringInfo_v1700__F2 (y : seq_type SIB1_v1700_IEs__uac_BarringInfo_v1700__list) :=
  match y with
  | (i0, _)=>
    make__SIB1_v1700_IEs__uac_BarringInfo_v1700__Type i0
  end.
Lemma SIB1_v1700_IEs__uac_BarringInfo_v1700__F1F2_cond (z : SIB1_v1700_IEs__uac_BarringInfo_v1700__Type)
  : SIB1_v1700_IEs__uac_BarringInfo_v1700__cond z ->
  (seq_cond SIB1_v1700_IEs__uac_BarringInfo_v1700__list (SIB1_v1700_IEs__uac_BarringInfo_v1700__F1 z)).
intro H. unfold SIB1_v1700_IEs__uac_BarringInfo_v1700__cond in H. simpl. auto. Qed.
Lemma SIB1_v1700_IEs__uac_BarringInfo_v1700__F1F2_cond2 (z : SIB1_v1700_IEs__uac_BarringInfo_v1700__Type)
 : SIB1_v1700_IEs__uac_BarringInfo_v1700__F2 (SIB1_v1700_IEs__uac_BarringInfo_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1_v1700_IEs__uac_BarringInfo_v1700__F2F1_cond (y : seq_type SIB1_v1700_IEs__uac_BarringInfo_v1700__list)
  : seq_cond SIB1_v1700_IEs__uac_BarringInfo_v1700__list y ->
 (SIB1_v1700_IEs__uac_BarringInfo_v1700__cond (SIB1_v1700_IEs__uac_BarringInfo_v1700__F2 y)) /\  SIB1_v1700_IEs__uac_BarringInfo_v1700__F1 (SIB1_v1700_IEs__uac_BarringInfo_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1_v1700_IEs__uac_BarringInfo_v1700__cond. simpl in *. auto.
 - simpl. unfold SIB1_v1700_IEs__uac_BarringInfo_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1_v1700_IEs__uac_BarringInfo_v1700__Format : T_Format SIB1_v1700_IEs__uac_BarringInfo_v1700__Type SIB1_v1700_IEs__uac_BarringInfo_v1700__cond :=
        proj2_format  SIB1_v1700_IEs__uac_BarringInfo_v1700__cond SIB1_v1700_IEs__uac_BarringInfo_v1700__list__Format
    SIB1_v1700_IEs__uac_BarringInfo_v1700__F1 SIB1_v1700_IEs__uac_BarringInfo_v1700__F2 SIB1_v1700_IEs__uac_BarringInfo_v1700__F1F2_cond  SIB1_v1700_IEs__uac_BarringInfo_v1700__F1F2_cond2 SIB1_v1700_IEs__uac_BarringInfo_v1700__F2F1_cond.
Opaque SIB1_v1700_IEs__uac_BarringInfo_v1700__cond SIB1_v1700_IEs__uac_BarringInfo_v1700__Format.


Definition SIB1_v1700_IEs__featurePriorities_r17__Format_Type := Eval cbn in seq_format_prod SIB1_v1700_IEs__featurePriorities_r17__list.
Definition SIB1_v1700_IEs__featurePriorities_r17__Format_list : SIB1_v1700_IEs__featurePriorities_r17__Format_Type :=
  (FeaturePriority_r17__Format, (FeaturePriority_r17__Format, (FeaturePriority_r17__Format, (FeaturePriority_r17__Format, unit_format)))).
Definition SIB1_v1700_IEs__featurePriorities_r17__list__Format := (*Eval compute in *) seq_format SIB1_v1700_IEs__featurePriorities_r17__list SIB1_v1700_IEs__featurePriorities_r17__Format_list.
Definition SIB1_v1700_IEs__featurePriorities_r17__F1 z :=
  (SIB1_v1700_IEs__featurePriorities_r17__redCapPriority_r17 z, (SIB1_v1700_IEs__featurePriorities_r17__slicingPriority_r17 z, (SIB1_v1700_IEs__featurePriorities_r17__msg3_Repetitions_Priority_r17 z, (SIB1_v1700_IEs__featurePriorities_r17__sdt_Priority_r17 z, tt)))).
Definition SIB1_v1700_IEs__featurePriorities_r17__F2 (y : seq_type SIB1_v1700_IEs__featurePriorities_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SIB1_v1700_IEs__featurePriorities_r17__Type i0 i1 i2 i3
  end.
Lemma SIB1_v1700_IEs__featurePriorities_r17__F1F2_cond (z : SIB1_v1700_IEs__featurePriorities_r17__Type)
  : SIB1_v1700_IEs__featurePriorities_r17__cond z ->
  (seq_cond SIB1_v1700_IEs__featurePriorities_r17__list (SIB1_v1700_IEs__featurePriorities_r17__F1 z)).
intro H. unfold SIB1_v1700_IEs__featurePriorities_r17__cond in H. simpl. auto. Qed.
Lemma SIB1_v1700_IEs__featurePriorities_r17__F1F2_cond2 (z : SIB1_v1700_IEs__featurePriorities_r17__Type)
 : SIB1_v1700_IEs__featurePriorities_r17__F2 (SIB1_v1700_IEs__featurePriorities_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1_v1700_IEs__featurePriorities_r17__F2F1_cond (y : seq_type SIB1_v1700_IEs__featurePriorities_r17__list)
  : seq_cond SIB1_v1700_IEs__featurePriorities_r17__list y ->
 (SIB1_v1700_IEs__featurePriorities_r17__cond (SIB1_v1700_IEs__featurePriorities_r17__F2 y)) /\  SIB1_v1700_IEs__featurePriorities_r17__F1 (SIB1_v1700_IEs__featurePriorities_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1_v1700_IEs__featurePriorities_r17__cond. simpl in *. auto.
 - simpl. unfold SIB1_v1700_IEs__featurePriorities_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1_v1700_IEs__featurePriorities_r17__Format : T_Format SIB1_v1700_IEs__featurePriorities_r17__Type SIB1_v1700_IEs__featurePriorities_r17__cond :=
        proj2_format  SIB1_v1700_IEs__featurePriorities_r17__cond SIB1_v1700_IEs__featurePriorities_r17__list__Format
    SIB1_v1700_IEs__featurePriorities_r17__F1 SIB1_v1700_IEs__featurePriorities_r17__F2 SIB1_v1700_IEs__featurePriorities_r17__F1F2_cond  SIB1_v1700_IEs__featurePriorities_r17__F1F2_cond2 SIB1_v1700_IEs__featurePriorities_r17__F2F1_cond.
Opaque SIB1_v1700_IEs__featurePriorities_r17__cond SIB1_v1700_IEs__featurePriorities_r17__Format.

Definition SIB1_v1700_IEs__hyperSFN_r17__Format : T_Format SIB1_v1700_IEs__hyperSFN_r17__Type SIB1_v1700_IEs__hyperSFN_r17__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque SIB1_v1700_IEs__hyperSFN_r17__cond SIB1_v1700_IEs__hyperSFN_r17__Format.

Definition SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Format : T_Format SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1_v1700_IEs__eDRX_AllowedIdle_r17__nat__Format SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F1 SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F2 SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F1F2 SIB1_v1700_IEs__eDRX_AllowedIdle_r17__F2F1.

Opaque SIB1_v1700_IEs__eDRX_AllowedIdle_r17__cond SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Format.

Definition SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Format : T_Format SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1_v1700_IEs__eDRX_AllowedInactive_r17__nat__Format SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F1 SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F2 SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F1F2 SIB1_v1700_IEs__eDRX_AllowedInactive_r17__F2F1.

Opaque SIB1_v1700_IEs__eDRX_AllowedInactive_r17__cond SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Format.

Definition SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Format : T_Format SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__nat__Format SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F1 SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F2 SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F1F2 SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__F2F1.

Opaque SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__cond SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Format.

Definition SIB1_v1700_IEs__cellBarredNTN_r17__Format : T_Format SIB1_v1700_IEs__cellBarredNTN_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1_v1700_IEs__cellBarredNTN_r17__nat__Format SIB1_v1700_IEs__cellBarredNTN_r17__F1 SIB1_v1700_IEs__cellBarredNTN_r17__F2 SIB1_v1700_IEs__cellBarredNTN_r17__F1F2 SIB1_v1700_IEs__cellBarredNTN_r17__F2F1.

Opaque SIB1_v1700_IEs__cellBarredNTN_r17__cond SIB1_v1700_IEs__cellBarredNTN_r17__Format.

Definition SIB1_v1700_IEs__nonCriticalExtension__helper : forall a : SIB1_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__SIB1_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition SIB1_v1700_IEs__nonCriticalExtension__Format : T_Format SIB1_v1700_IEs__nonCriticalExtension__Type SIB1_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SIB1_v1700_IEs__nonCriticalExtension__Type)
    SIB1_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque SIB1_v1700_IEs__nonCriticalExtension__cond SIB1_v1700_IEs__nonCriticalExtension__Format.


Definition SIB1_v1700_IEs__Format_Type := Eval cbn in seq_format_prod SIB1_v1700_IEs__list.
Definition SIB1_v1700_IEs__Format_list : SIB1_v1700_IEs__Format_Type :=
  (SIB1_v1700_IEs__hsdn_Cell_r17__Format, (SIB1_v1700_IEs__uac_BarringInfo_v1700__Format, (SDT_ConfigCommonSIB_r17__Format, (RedCap_ConfigCommonSIB_r17__Format, (SIB1_v1700_IEs__featurePriorities_r17__Format, (SI_SchedulingInfo_v1700__Format, (SIB1_v1700_IEs__hyperSFN_r17__Format, (SIB1_v1700_IEs__eDRX_AllowedIdle_r17__Format, (SIB1_v1700_IEs__eDRX_AllowedInactive_r17__Format, (SIB1_v1700_IEs__intraFreqReselectionRedCap_r17__Format, (SIB1_v1700_IEs__cellBarredNTN_r17__Format, (SIB1_v1700_IEs__nonCriticalExtension__Format, unit_format)))))))))))).
Definition SIB1_v1700_IEs__list__Format := (*Eval compute in *) seq_format SIB1_v1700_IEs__list SIB1_v1700_IEs__Format_list.
Definition SIB1_v1700_IEs__F1 z :=
  (SIB1_v1700_IEs__hsdn_Cell_r17 z, (SIB1_v1700_IEs__uac_BarringInfo_v1700 z, (SIB1_v1700_IEs__sdt_ConfigCommon_r17 z, (SIB1_v1700_IEs__redCap_ConfigCommon_r17 z, (SIB1_v1700_IEs__featurePriorities_r17 z, (SIB1_v1700_IEs__si_SchedulingInfo_v1700 z, (SIB1_v1700_IEs__hyperSFN_r17 z, (SIB1_v1700_IEs__eDRX_AllowedIdle_r17 z, (SIB1_v1700_IEs__eDRX_AllowedInactive_r17 z, (SIB1_v1700_IEs__intraFreqReselectionRedCap_r17 z, (SIB1_v1700_IEs__cellBarredNTN_r17 z, (SIB1_v1700_IEs__nonCriticalExtension z, tt)))))))))))).
Definition SIB1_v1700_IEs__F2 (y : seq_type SIB1_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, _))))))))))))=>
    make__SIB1_v1700_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  end.
Lemma SIB1_v1700_IEs__F1F2_cond (z : SIB1_v1700_IEs__Type)
  : SIB1_v1700_IEs__cond z ->
  (seq_cond SIB1_v1700_IEs__list (SIB1_v1700_IEs__F1 z)).
intro H. unfold SIB1_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma SIB1_v1700_IEs__F1F2_cond2 (z : SIB1_v1700_IEs__Type)
 : SIB1_v1700_IEs__F2 (SIB1_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1_v1700_IEs__F2F1_cond (y : seq_type SIB1_v1700_IEs__list)
  : seq_cond SIB1_v1700_IEs__list y ->
 (SIB1_v1700_IEs__cond (SIB1_v1700_IEs__F2 y)) /\  SIB1_v1700_IEs__F1 (SIB1_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold SIB1_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1_v1700_IEs__Format : T_Format SIB1_v1700_IEs__Type SIB1_v1700_IEs__cond :=
        proj2_format  SIB1_v1700_IEs__cond SIB1_v1700_IEs__list__Format
    SIB1_v1700_IEs__F1 SIB1_v1700_IEs__F2 SIB1_v1700_IEs__F1F2_cond  SIB1_v1700_IEs__F1F2_cond2 SIB1_v1700_IEs__F2F1_cond.
Opaque SIB1_v1700_IEs__cond SIB1_v1700_IEs__Format.

