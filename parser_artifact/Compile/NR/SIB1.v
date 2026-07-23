Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.Q_RxLevMin.

Opaque Q_RxLevMin__cond Q_RxLevMin__Format.

Lemma SIB1__cellSelectionInfo__q_RxLevMinOffset__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SIB1__cellSelectionInfo__q_RxLevMinOffset__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SIB1__cellSelectionInfo__q_RxLevMinOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB1__cellSelectionInfo__q_RxLevMinOffset__Type := Z.
Definition SIB1__cellSelectionInfo__q_RxLevMinOffset__cond := (fun z => (1 <= z <= 8)%Z).
Require Import NR.Q_RxLevMin.

Opaque Q_RxLevMin__cond Q_RxLevMin__Format.

Require Import NR.Q_QualMin.

Opaque Q_QualMin__cond Q_QualMin__Format.

Lemma SIB1__cellSelectionInfo__q_QualMinOffset__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SIB1__cellSelectionInfo__q_QualMinOffset__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SIB1__cellSelectionInfo__q_QualMinOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB1__cellSelectionInfo__q_QualMinOffset__Type := Z.
Definition SIB1__cellSelectionInfo__q_QualMinOffset__cond := (fun z => (1 <= z <= 8)%Z).
Record SIB1__cellSelectionInfo__Type : Set :=
  make__SIB1__cellSelectionInfo__Type {
    SIB1__cellSelectionInfo__q_RxLevMin : Q_RxLevMin__Type ;
    SIB1__cellSelectionInfo__q_RxLevMinOffset : option Z ;
    SIB1__cellSelectionInfo__q_RxLevMinSUL : option Q_RxLevMin__Type ;
    SIB1__cellSelectionInfo__q_QualMin : option Q_QualMin__Type ;
    SIB1__cellSelectionInfo__q_QualMinOffset : option Z ;
}.
Definition SIB1__cellSelectionInfo__list := (
 Nor Q_RxLevMin__Type Q_RxLevMin__cond ::
 Opt Z SIB1__cellSelectionInfo__q_RxLevMinOffset__cond ::
 Opt Q_RxLevMin__Type Q_RxLevMin__cond ::
 Opt Q_QualMin__Type Q_QualMin__cond ::
 Opt Z SIB1__cellSelectionInfo__q_QualMinOffset__cond ::
 nil).
Definition SIB1__cellSelectionInfo__cond z := 
  Q_RxLevMin__cond (SIB1__cellSelectionInfo__q_RxLevMin z) /\
  opt_cond SIB1__cellSelectionInfo__q_RxLevMinOffset__cond (SIB1__cellSelectionInfo__q_RxLevMinOffset z) /\
  opt_cond Q_RxLevMin__cond (SIB1__cellSelectionInfo__q_RxLevMinSUL z) /\
  opt_cond Q_QualMin__cond (SIB1__cellSelectionInfo__q_QualMin z) /\
  opt_cond SIB1__cellSelectionInfo__q_QualMinOffset__cond (SIB1__cellSelectionInfo__q_QualMinOffset z) /\
  True.

Require Import NR.CellAccessRelatedInfo.

Opaque CellAccessRelatedInfo__cond CellAccessRelatedInfo__Format.

Require Import NR.ConnEstFailureControl.

Opaque ConnEstFailureControl__cond ConnEstFailureControl__Format.

Require Import NR.SI_SchedulingInfo.

Opaque SI_SchedulingInfo__cond SI_SchedulingInfo__Format.

Require Import NR.ServingCellConfigCommonSIB.

Opaque ServingCellConfigCommonSIB__cond ServingCellConfigCommonSIB__Format.

Inductive SIB1__ims_EmergencySupport__Type : Set :=
 | SIB1__ims_EmergencySupport__true
.
Definition SIB1__ims_EmergencySupport__cond := (fun (_ : SIB1__ims_EmergencySupport__Type) => True).
Lemma SIB1__ims_EmergencySupport__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1__ims_EmergencySupport__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB1__ims_EmergencySupport__nat__helper.

Definition SIB1__ims_EmergencySupport__F1 t :=
  match t with
  | SIB1__ims_EmergencySupport__true => 0
  end.
Definition SIB1__ims_EmergencySupport__F2 n :=
  match n with
  | 0 => SIB1__ims_EmergencySupport__true
  | _ => SIB1__ims_EmergencySupport__true
  end.
Lemma SIB1__ims_EmergencySupport__F1F2 : forall x : SIB1__ims_EmergencySupport__Type, (SIB1__ims_EmergencySupport__F1 x <= 0) /\ SIB1__ims_EmergencySupport__F2 (SIB1__ims_EmergencySupport__F1 x) = x. imp_solve. Qed.
Lemma SIB1__ims_EmergencySupport__F2F1 : forall (y : nat) (H : y <= 0), SIB1__ims_EmergencySupport__F1 (SIB1__ims_EmergencySupport__F2 y) = y. enum_solve H y. Qed.

Inductive SIB1__eCallOverIMS_Support__Type : Set :=
 | SIB1__eCallOverIMS_Support__true
.
Definition SIB1__eCallOverIMS_Support__cond := (fun (_ : SIB1__eCallOverIMS_Support__Type) => True).
Lemma SIB1__eCallOverIMS_Support__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1__eCallOverIMS_Support__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB1__eCallOverIMS_Support__nat__helper.

Definition SIB1__eCallOverIMS_Support__F1 t :=
  match t with
  | SIB1__eCallOverIMS_Support__true => 0
  end.
Definition SIB1__eCallOverIMS_Support__F2 n :=
  match n with
  | 0 => SIB1__eCallOverIMS_Support__true
  | _ => SIB1__eCallOverIMS_Support__true
  end.
Lemma SIB1__eCallOverIMS_Support__F1F2 : forall x : SIB1__eCallOverIMS_Support__Type, (SIB1__eCallOverIMS_Support__F1 x <= 0) /\ SIB1__eCallOverIMS_Support__F2 (SIB1__eCallOverIMS_Support__F1 x) = x. imp_solve. Qed.
Lemma SIB1__eCallOverIMS_Support__F2F1 : forall (y : nat) (H : y <= 0), SIB1__eCallOverIMS_Support__F1 (SIB1__eCallOverIMS_Support__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UE_TimersAndConstants.

Opaque UE_TimersAndConstants__cond UE_TimersAndConstants__Format.

Require Import NR.UAC_BarringPerCatList.

Opaque UAC_BarringPerCatList__cond UAC_BarringPerCatList__Format.

Require Import NR.UAC_BarringPerPLMN_List.

Opaque UAC_BarringPerPLMN_List__cond UAC_BarringPerPLMN_List__Format.

Require Import NR.UAC_BarringInfoSetList.

Opaque UAC_BarringInfoSetList__cond UAC_BarringInfoSetList__Format.

Require Import NR.UAC_AccessCategory1_SelectionAssistanceInfo.

Opaque UAC_AccessCategory1_SelectionAssistanceInfo__cond UAC_AccessCategory1_SelectionAssistanceInfo__Format.

Require Import NR.UAC_AccessCategory1_SelectionAssistanceInfo.

Opaque UAC_AccessCategory1_SelectionAssistanceInfo__cond UAC_AccessCategory1_SelectionAssistanceInfo__Format.

Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Type := list UAC_AccessCategory1_SelectionAssistanceInfo__Type.

Lemma SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__helper1 : (0 <= 2 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 2))%Z). { apply Zorder.Zle_minus_le_0. apply SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__cond (z : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Type) :=  (2 <= Z.of_nat (length z) <= maxPLMN)%Z /\ (list_and UAC_AccessCategory1_SelectionAssistanceInfo__cond z) .


Inductive SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type : Set :=
  | SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__plmnCommon : UAC_AccessCategory1_SelectionAssistanceInfo__Type -> SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type
  | SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Type -> SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type
.
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list : list typ := (
typ_cons UAC_AccessCategory1_SelectionAssistanceInfo__Type UAC_AccessCategory1_SelectionAssistanceInfo__cond ::
typ_cons SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Type SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__cond ::
 nil).
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__cond (c : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type) := 
  match c with
  | SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__plmnCommon t => UAC_AccessCategory1_SelectionAssistanceInfo__cond t 
  | SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList t => SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__cond t 
  end.

Lemma SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__len_helper1 : to_bit_sz (length SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__len_helper2 : 2 <= length2 SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list.
 simpl. lia. Qed.
Record SIB1__uac_BarringInfo__Type : Set :=
  make__SIB1__uac_BarringInfo__Type {
    SIB1__uac_BarringInfo__uac_BarringForCommon : option UAC_BarringPerCatList__Type ;
    SIB1__uac_BarringInfo__uac_BarringPerPLMN_List : option UAC_BarringPerPLMN_List__Type ;
    SIB1__uac_BarringInfo__uac_BarringInfoSetList : UAC_BarringInfoSetList__Type ;
    SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo : option SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type ;
}.
Definition SIB1__uac_BarringInfo__list := (
 Opt UAC_BarringPerCatList__Type UAC_BarringPerCatList__cond ::
 Opt UAC_BarringPerPLMN_List__Type UAC_BarringPerPLMN_List__cond ::
 Nor UAC_BarringInfoSetList__Type UAC_BarringInfoSetList__cond ::
 Opt SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__cond ::
 nil).
Definition SIB1__uac_BarringInfo__cond z := 
  opt_cond UAC_BarringPerCatList__cond (SIB1__uac_BarringInfo__uac_BarringForCommon z) /\
  opt_cond UAC_BarringPerPLMN_List__cond (SIB1__uac_BarringInfo__uac_BarringPerPLMN_List z) /\
  UAC_BarringInfoSetList__cond (SIB1__uac_BarringInfo__uac_BarringInfoSetList z) /\
  opt_cond SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__cond (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo z) /\
  True.

Inductive SIB1__useFullResumeID__Type : Set :=
 | SIB1__useFullResumeID__true
.
Definition SIB1__useFullResumeID__cond := (fun (_ : SIB1__useFullResumeID__Type) => True).
Lemma SIB1__useFullResumeID__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB1__useFullResumeID__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB1__useFullResumeID__nat__helper.

Definition SIB1__useFullResumeID__F1 t :=
  match t with
  | SIB1__useFullResumeID__true => 0
  end.
Definition SIB1__useFullResumeID__F2 n :=
  match n with
  | 0 => SIB1__useFullResumeID__true
  | _ => SIB1__useFullResumeID__true
  end.
Lemma SIB1__useFullResumeID__F1F2 : forall x : SIB1__useFullResumeID__Type, (SIB1__useFullResumeID__F1 x <= 0) /\ SIB1__useFullResumeID__F2 (SIB1__useFullResumeID__F1 x) = x. imp_solve. Qed.
Lemma SIB1__useFullResumeID__F2F1 : forall (y : nat) (H : y <= 0), SIB1__useFullResumeID__F1 (SIB1__useFullResumeID__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SIB1_v1610_IEs.

Opaque SIB1_v1610_IEs__cond SIB1_v1610_IEs__Format.

Record SIB1__Type : Set :=
  make__SIB1__Type {
    SIB1__cellSelectionInfo : option SIB1__cellSelectionInfo__Type ;
    SIB1__cellAccessRelatedInfo : CellAccessRelatedInfo__Type ;
    SIB1__connEstFailureControl : option ConnEstFailureControl__Type ;
    SIB1__si_SchedulingInfo : option SI_SchedulingInfo__Type ;
    SIB1__servingCellConfigCommon : option ServingCellConfigCommonSIB__Type ;
    SIB1__ims_EmergencySupport : option SIB1__ims_EmergencySupport__Type ;
    SIB1__eCallOverIMS_Support : option SIB1__eCallOverIMS_Support__Type ;
    SIB1__ue_TimersAndConstants : option UE_TimersAndConstants__Type ;
    SIB1__uac_BarringInfo : option SIB1__uac_BarringInfo__Type ;
    SIB1__useFullResumeID : option SIB1__useFullResumeID__Type ;
    SIB1__lateNonCriticalExtension : option octet_string ;
    SIB1__nonCriticalExtension : option SIB1_v1610_IEs__Type ;
}.
Definition SIB1__list := (
 Opt SIB1__cellSelectionInfo__Type SIB1__cellSelectionInfo__cond ::
 Nor CellAccessRelatedInfo__Type CellAccessRelatedInfo__cond ::
 Opt ConnEstFailureControl__Type ConnEstFailureControl__cond ::
 Opt SI_SchedulingInfo__Type SI_SchedulingInfo__cond ::
 Opt ServingCellConfigCommonSIB__Type ServingCellConfigCommonSIB__cond ::
 Opt SIB1__ims_EmergencySupport__Type SIB1__ims_EmergencySupport__cond ::
 Opt SIB1__eCallOverIMS_Support__Type SIB1__eCallOverIMS_Support__cond ::
 Opt UE_TimersAndConstants__Type UE_TimersAndConstants__cond ::
 Opt SIB1__uac_BarringInfo__Type SIB1__uac_BarringInfo__cond ::
 Opt SIB1__useFullResumeID__Type SIB1__useFullResumeID__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SIB1_v1610_IEs__Type SIB1_v1610_IEs__cond ::
 nil).
Definition SIB1__cond z := 
  opt_cond SIB1__cellSelectionInfo__cond (SIB1__cellSelectionInfo z) /\
  CellAccessRelatedInfo__cond (SIB1__cellAccessRelatedInfo z) /\
  opt_cond ConnEstFailureControl__cond (SIB1__connEstFailureControl z) /\
  opt_cond SI_SchedulingInfo__cond (SIB1__si_SchedulingInfo z) /\
  opt_cond ServingCellConfigCommonSIB__cond (SIB1__servingCellConfigCommon z) /\
  opt_cond SIB1__ims_EmergencySupport__cond (SIB1__ims_EmergencySupport z) /\
  opt_cond SIB1__eCallOverIMS_Support__cond (SIB1__eCallOverIMS_Support z) /\
  opt_cond UE_TimersAndConstants__cond (SIB1__ue_TimersAndConstants z) /\
  opt_cond SIB1__uac_BarringInfo__cond (SIB1__uac_BarringInfo z) /\
  opt_cond SIB1__useFullResumeID__cond (SIB1__useFullResumeID z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB1__lateNonCriticalExtension z) /\
  opt_cond SIB1_v1610_IEs__cond (SIB1__nonCriticalExtension z) /\
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
Definition SIB1__cellSelectionInfo__q_RxLevMinOffset__Format : T_Format Z SIB1__cellSelectionInfo__q_RxLevMinOffset__cond :=
 ranged_int_format (1) (8) SIB1__cellSelectionInfo__q_RxLevMinOffset__helper1 SIB1__cellSelectionInfo__q_RxLevMinOffset__helper2.

Opaque SIB1__cellSelectionInfo__q_RxLevMinOffset__cond SIB1__cellSelectionInfo__q_RxLevMinOffset__Format.

Definition SIB1__cellSelectionInfo__q_QualMinOffset__Format : T_Format Z SIB1__cellSelectionInfo__q_QualMinOffset__cond :=
 ranged_int_format (1) (8) SIB1__cellSelectionInfo__q_QualMinOffset__helper1 SIB1__cellSelectionInfo__q_QualMinOffset__helper2.

Opaque SIB1__cellSelectionInfo__q_QualMinOffset__cond SIB1__cellSelectionInfo__q_QualMinOffset__Format.


Definition SIB1__cellSelectionInfo__Format_Type := Eval cbn in seq_format_prod SIB1__cellSelectionInfo__list.
Definition SIB1__cellSelectionInfo__Format_list : SIB1__cellSelectionInfo__Format_Type :=
  (Q_RxLevMin__Format, (SIB1__cellSelectionInfo__q_RxLevMinOffset__Format, (Q_RxLevMin__Format, (Q_QualMin__Format, (SIB1__cellSelectionInfo__q_QualMinOffset__Format, unit_format))))).
Definition SIB1__cellSelectionInfo__list__Format := (*Eval compute in *) seq_format SIB1__cellSelectionInfo__list SIB1__cellSelectionInfo__Format_list.
Definition SIB1__cellSelectionInfo__F1 z :=
  (SIB1__cellSelectionInfo__q_RxLevMin z, (SIB1__cellSelectionInfo__q_RxLevMinOffset z, (SIB1__cellSelectionInfo__q_RxLevMinSUL z, (SIB1__cellSelectionInfo__q_QualMin z, (SIB1__cellSelectionInfo__q_QualMinOffset z, tt))))).
Definition SIB1__cellSelectionInfo__F2 (y : seq_type SIB1__cellSelectionInfo__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SIB1__cellSelectionInfo__Type i0 i1 i2 i3 i4
  end.
Lemma SIB1__cellSelectionInfo__F1F2_cond (z : SIB1__cellSelectionInfo__Type)
  : SIB1__cellSelectionInfo__cond z ->
  (seq_cond SIB1__cellSelectionInfo__list (SIB1__cellSelectionInfo__F1 z)).
intro H. unfold SIB1__cellSelectionInfo__cond in H. simpl. auto. Qed.
Lemma SIB1__cellSelectionInfo__F1F2_cond2 (z : SIB1__cellSelectionInfo__Type)
 : SIB1__cellSelectionInfo__F2 (SIB1__cellSelectionInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1__cellSelectionInfo__F2F1_cond (y : seq_type SIB1__cellSelectionInfo__list)
  : seq_cond SIB1__cellSelectionInfo__list y ->
 (SIB1__cellSelectionInfo__cond (SIB1__cellSelectionInfo__F2 y)) /\  SIB1__cellSelectionInfo__F1 (SIB1__cellSelectionInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1__cellSelectionInfo__cond. simpl in *. auto.
 - simpl. unfold SIB1__cellSelectionInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1__cellSelectionInfo__Format : T_Format SIB1__cellSelectionInfo__Type SIB1__cellSelectionInfo__cond :=
        proj2_format  SIB1__cellSelectionInfo__cond SIB1__cellSelectionInfo__list__Format
    SIB1__cellSelectionInfo__F1 SIB1__cellSelectionInfo__F2 SIB1__cellSelectionInfo__F1F2_cond  SIB1__cellSelectionInfo__F1F2_cond2 SIB1__cellSelectionInfo__F2F1_cond.
Opaque SIB1__cellSelectionInfo__cond SIB1__cellSelectionInfo__Format.

Definition SIB1__ims_EmergencySupport__Format : T_Format SIB1__ims_EmergencySupport__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1__ims_EmergencySupport__nat__Format SIB1__ims_EmergencySupport__F1 SIB1__ims_EmergencySupport__F2 SIB1__ims_EmergencySupport__F1F2 SIB1__ims_EmergencySupport__F2F1.

Opaque SIB1__ims_EmergencySupport__cond SIB1__ims_EmergencySupport__Format.

Definition SIB1__eCallOverIMS_Support__Format : T_Format SIB1__eCallOverIMS_Support__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1__eCallOverIMS_Support__nat__Format SIB1__eCallOverIMS_Support__F1 SIB1__eCallOverIMS_Support__F2 SIB1__eCallOverIMS_Support__F1F2 SIB1__eCallOverIMS_Support__F2F1.

Opaque SIB1__eCallOverIMS_Support__cond SIB1__eCallOverIMS_Support__Format.

Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Format : T_Format SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Type SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__cond := seq_of_format UAC_AccessCategory1_SelectionAssistanceInfo__Format 2 maxPLMN SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__helper1 SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__helper2.

Opaque SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__cond SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Format.


Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Format_Type := Eval cbn in get_formats SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list.
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Format_list : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Format_Type :=
  (UAC_AccessCategory1_SelectionAssistanceInfo__Format, (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Format, unit__Format)).
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list__Format := Eval compute in choice_format SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__len_helper1 SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__len_helper2  SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Format_list.
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F1 (z : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type) : (choice SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list) :=
  match z with
   | SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__plmnCommon t => existT _ 0 t
  | SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList t => existT _ 1 t
  end.
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__g := (fun n => typ_set (get_nth_typ SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list n)).
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F2 (y : choice SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list) : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__g n -> SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type) with
    | 0 => fun (t : UAC_AccessCategory1_SelectionAssistanceInfo__Type) => SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__plmnCommon t 
    | 1 => fun (t : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList__Type) => SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__individualPLMNList t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type with end) n0
           end t0).

Lemma SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__helper2 :  forall (y : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type), SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__cond y -> choice_cond SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__helper3 :  forall (y : SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type), SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F2 (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__helper4 : (forall b : choice SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list, choice_cond SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list b -> SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__cond (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F2 b) /\ SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F1 (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F1 SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F2.
Definition SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Format : T_Format SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Type SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__cond :=
  (* Eval compute in *) proj2_format SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__cond SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__list__Format SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F1 SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__F2 SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__helper2 SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__helper3 SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__helper4.
Opaque SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__cond SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Format.


Definition SIB1__uac_BarringInfo__Format_Type := Eval cbn in seq_format_prod SIB1__uac_BarringInfo__list.
Definition SIB1__uac_BarringInfo__Format_list : SIB1__uac_BarringInfo__Format_Type :=
  (UAC_BarringPerCatList__Format, (UAC_BarringPerPLMN_List__Format, (UAC_BarringInfoSetList__Format, (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo__Format, unit_format)))).
Definition SIB1__uac_BarringInfo__list__Format := (*Eval compute in *) seq_format SIB1__uac_BarringInfo__list SIB1__uac_BarringInfo__Format_list.
Definition SIB1__uac_BarringInfo__F1 z :=
  (SIB1__uac_BarringInfo__uac_BarringForCommon z, (SIB1__uac_BarringInfo__uac_BarringPerPLMN_List z, (SIB1__uac_BarringInfo__uac_BarringInfoSetList z, (SIB1__uac_BarringInfo__uac_AccessCategory1_SelectionAssistanceInfo z, tt)))).
Definition SIB1__uac_BarringInfo__F2 (y : seq_type SIB1__uac_BarringInfo__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SIB1__uac_BarringInfo__Type i0 i1 i2 i3
  end.
Lemma SIB1__uac_BarringInfo__F1F2_cond (z : SIB1__uac_BarringInfo__Type)
  : SIB1__uac_BarringInfo__cond z ->
  (seq_cond SIB1__uac_BarringInfo__list (SIB1__uac_BarringInfo__F1 z)).
intro H. unfold SIB1__uac_BarringInfo__cond in H. simpl. auto. Qed.
Lemma SIB1__uac_BarringInfo__F1F2_cond2 (z : SIB1__uac_BarringInfo__Type)
 : SIB1__uac_BarringInfo__F2 (SIB1__uac_BarringInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1__uac_BarringInfo__F2F1_cond (y : seq_type SIB1__uac_BarringInfo__list)
  : seq_cond SIB1__uac_BarringInfo__list y ->
 (SIB1__uac_BarringInfo__cond (SIB1__uac_BarringInfo__F2 y)) /\  SIB1__uac_BarringInfo__F1 (SIB1__uac_BarringInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1__uac_BarringInfo__cond. simpl in *. auto.
 - simpl. unfold SIB1__uac_BarringInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1__uac_BarringInfo__Format : T_Format SIB1__uac_BarringInfo__Type SIB1__uac_BarringInfo__cond :=
        proj2_format  SIB1__uac_BarringInfo__cond SIB1__uac_BarringInfo__list__Format
    SIB1__uac_BarringInfo__F1 SIB1__uac_BarringInfo__F2 SIB1__uac_BarringInfo__F1F2_cond  SIB1__uac_BarringInfo__F1F2_cond2 SIB1__uac_BarringInfo__F2F1_cond.
Opaque SIB1__uac_BarringInfo__cond SIB1__uac_BarringInfo__Format.

Definition SIB1__useFullResumeID__Format : T_Format SIB1__useFullResumeID__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB1__useFullResumeID__nat__Format SIB1__useFullResumeID__F1 SIB1__useFullResumeID__F2 SIB1__useFullResumeID__F1F2 SIB1__useFullResumeID__F2F1.

Opaque SIB1__useFullResumeID__cond SIB1__useFullResumeID__Format.


Definition SIB1__Format_Type := Eval cbn in seq_format_prod SIB1__list.
Definition SIB1__Format_list : SIB1__Format_Type :=
  (SIB1__cellSelectionInfo__Format, (CellAccessRelatedInfo__Format, (ConnEstFailureControl__Format, (SI_SchedulingInfo__Format, (ServingCellConfigCommonSIB__Format, (SIB1__ims_EmergencySupport__Format, (SIB1__eCallOverIMS_Support__Format, (UE_TimersAndConstants__Format, (SIB1__uac_BarringInfo__Format, (SIB1__useFullResumeID__Format, (octet_string_nc__Format, (SIB1_v1610_IEs__Format, unit_format)))))))))))).
Definition SIB1__list__Format := (*Eval compute in *) seq_format SIB1__list SIB1__Format_list.
Definition SIB1__F1 z :=
  (SIB1__cellSelectionInfo z, (SIB1__cellAccessRelatedInfo z, (SIB1__connEstFailureControl z, (SIB1__si_SchedulingInfo z, (SIB1__servingCellConfigCommon z, (SIB1__ims_EmergencySupport z, (SIB1__eCallOverIMS_Support z, (SIB1__ue_TimersAndConstants z, (SIB1__uac_BarringInfo z, (SIB1__useFullResumeID z, (SIB1__lateNonCriticalExtension z, (SIB1__nonCriticalExtension z, tt)))))))))))).
Definition SIB1__F2 (y : seq_type SIB1__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, _))))))))))))=>
    make__SIB1__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  end.
Lemma SIB1__F1F2_cond (z : SIB1__Type)
  : SIB1__cond z ->
  (seq_cond SIB1__list (SIB1__F1 z)).
intro H. unfold SIB1__cond in H. simpl. auto. Qed.
Lemma SIB1__F1F2_cond2 (z : SIB1__Type)
 : SIB1__F2 (SIB1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB1__F2F1_cond (y : seq_type SIB1__list)
  : seq_cond SIB1__list y ->
 (SIB1__cond (SIB1__F2 y)) /\  SIB1__F1 (SIB1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB1__cond. simpl in *. auto.
 - simpl. unfold SIB1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB1__Format : T_Format SIB1__Type SIB1__cond :=
        proj2_format  SIB1__cond SIB1__list__Format
    SIB1__F1 SIB1__F2 SIB1__F1F2_cond  SIB1__F1F2_cond2 SIB1__F2F1_cond.
Opaque SIB1__cond SIB1__Format.

