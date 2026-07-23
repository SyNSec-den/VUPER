Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.MeasResultList2NR.

Opaque MeasResultList2NR__cond MeasResultList2NR__Format.

Require Import NR.MeasResultCellListSFTD_NR.

Opaque MeasResultCellListSFTD_NR__cond MeasResultCellListSFTD_NR__Format.

Inductive CG_ConfigInfo_IEs__scgFailureInfo__failureType__Type : Set :=
 | CG_ConfigInfo_IEs__scgFailureInfo__failureType__t310_Expiry
 | CG_ConfigInfo_IEs__scgFailureInfo__failureType__randomAccessProblem
 | CG_ConfigInfo_IEs__scgFailureInfo__failureType__rlc_MaxNumRetx
 | CG_ConfigInfo_IEs__scgFailureInfo__failureType__synchReconfigFailure_SCG
 | CG_ConfigInfo_IEs__scgFailureInfo__failureType__scg_reconfigFailure
 | CG_ConfigInfo_IEs__scgFailureInfo__failureType__srb3_IntegrityFailure
.
Definition CG_ConfigInfo_IEs__scgFailureInfo__failureType__cond := (fun (_ : CG_ConfigInfo_IEs__scgFailureInfo__failureType__Type) => True).
Lemma CG_ConfigInfo_IEs__scgFailureInfo__failureType__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_ConfigInfo_IEs__scgFailureInfo__failureType__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 CG_ConfigInfo_IEs__scgFailureInfo__failureType__nat__helper.

Definition CG_ConfigInfo_IEs__scgFailureInfo__failureType__F1 t :=
  match t with
  | CG_ConfigInfo_IEs__scgFailureInfo__failureType__t310_Expiry => 0
  | CG_ConfigInfo_IEs__scgFailureInfo__failureType__randomAccessProblem => 1
  | CG_ConfigInfo_IEs__scgFailureInfo__failureType__rlc_MaxNumRetx => 2
  | CG_ConfigInfo_IEs__scgFailureInfo__failureType__synchReconfigFailure_SCG => 3
  | CG_ConfigInfo_IEs__scgFailureInfo__failureType__scg_reconfigFailure => 4
  | CG_ConfigInfo_IEs__scgFailureInfo__failureType__srb3_IntegrityFailure => 5
  end.
Definition CG_ConfigInfo_IEs__scgFailureInfo__failureType__F2 n :=
  match n with
  | 0 => CG_ConfigInfo_IEs__scgFailureInfo__failureType__t310_Expiry
  | 1 => CG_ConfigInfo_IEs__scgFailureInfo__failureType__randomAccessProblem
  | 2 => CG_ConfigInfo_IEs__scgFailureInfo__failureType__rlc_MaxNumRetx
  | 3 => CG_ConfigInfo_IEs__scgFailureInfo__failureType__synchReconfigFailure_SCG
  | 4 => CG_ConfigInfo_IEs__scgFailureInfo__failureType__scg_reconfigFailure
  | 5 => CG_ConfigInfo_IEs__scgFailureInfo__failureType__srb3_IntegrityFailure
  | _ => CG_ConfigInfo_IEs__scgFailureInfo__failureType__t310_Expiry
  end.
Lemma CG_ConfigInfo_IEs__scgFailureInfo__failureType__F1F2 : forall x : CG_ConfigInfo_IEs__scgFailureInfo__failureType__Type, (CG_ConfigInfo_IEs__scgFailureInfo__failureType__F1 x <= 5) /\ CG_ConfigInfo_IEs__scgFailureInfo__failureType__F2 (CG_ConfigInfo_IEs__scgFailureInfo__failureType__F1 x) = x. imp_solve. Qed.
Lemma CG_ConfigInfo_IEs__scgFailureInfo__failureType__F2F1 : forall (y : nat) (H : y <= 5), CG_ConfigInfo_IEs__scgFailureInfo__failureType__F1 (CG_ConfigInfo_IEs__scgFailureInfo__failureType__F2 y) = y. enum_solve H y. Qed.

Record CG_ConfigInfo_IEs__scgFailureInfo__Type : Set :=
  make__CG_ConfigInfo_IEs__scgFailureInfo__Type {
    CG_ConfigInfo_IEs__scgFailureInfo__failureType : CG_ConfigInfo_IEs__scgFailureInfo__failureType__Type ;
    CG_ConfigInfo_IEs__scgFailureInfo__measResultSCG : octet_string ;
}.
Definition CG_ConfigInfo_IEs__scgFailureInfo__list := (
 Nor CG_ConfigInfo_IEs__scgFailureInfo__failureType__Type CG_ConfigInfo_IEs__scgFailureInfo__failureType__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition CG_ConfigInfo_IEs__scgFailureInfo__cond z := 
  CG_ConfigInfo_IEs__scgFailureInfo__failureType__cond (CG_ConfigInfo_IEs__scgFailureInfo__failureType z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_IEs__scgFailureInfo__measResultSCG z) /\
  True.

Require Import NR.ConfigRestrictInfoSCG.

Opaque ConfigRestrictInfoSCG__cond ConfigRestrictInfoSCG__Format.

Require Import NR.DRX_Info.

Opaque DRX_Info__cond DRX_Info__Format.

Require Import NR.MeasConfigMN.

Opaque MeasConfigMN__cond MeasConfigMN__Format.

Require Import NR.MRDC_AssistanceInfo.

Opaque MRDC_AssistanceInfo__cond MRDC_AssistanceInfo__Format.

Require Import NR.CG_ConfigInfo_v1540_IEs.

Opaque CG_ConfigInfo_v1540_IEs__cond CG_ConfigInfo_v1540_IEs__Format.

Record CG_ConfigInfo_IEs__Type : Set :=
  make__CG_ConfigInfo_IEs__Type {
    CG_ConfigInfo_IEs__ue_CapabilityInfo : option octet_string ;
    CG_ConfigInfo_IEs__candidateCellInfoListMN : option MeasResultList2NR__Type ;
    CG_ConfigInfo_IEs__candidateCellInfoListSN : option octet_string ;
    CG_ConfigInfo_IEs__measResultCellListSFTD_NR : option MeasResultCellListSFTD_NR__Type ;
    CG_ConfigInfo_IEs__scgFailureInfo : option CG_ConfigInfo_IEs__scgFailureInfo__Type ;
    CG_ConfigInfo_IEs__configRestrictInfo : option ConfigRestrictInfoSCG__Type ;
    CG_ConfigInfo_IEs__drx_InfoMCG : option DRX_Info__Type ;
    CG_ConfigInfo_IEs__measConfigMN : option MeasConfigMN__Type ;
    CG_ConfigInfo_IEs__sourceConfigSCG : option octet_string ;
    CG_ConfigInfo_IEs__scg_RB_Config : option octet_string ;
    CG_ConfigInfo_IEs__mcg_RB_Config : option octet_string ;
    CG_ConfigInfo_IEs__mrdc_AssistanceInfo : option MRDC_AssistanceInfo__Type ;
    CG_ConfigInfo_IEs__nonCriticalExtension : option CG_ConfigInfo_v1540_IEs__Type ;
}.
Definition CG_ConfigInfo_IEs__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MeasResultList2NR__Type MeasResultList2NR__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MeasResultCellListSFTD_NR__Type MeasResultCellListSFTD_NR__cond ::
 Opt CG_ConfigInfo_IEs__scgFailureInfo__Type CG_ConfigInfo_IEs__scgFailureInfo__cond ::
 Opt ConfigRestrictInfoSCG__Type ConfigRestrictInfoSCG__cond ::
 Opt DRX_Info__Type DRX_Info__cond ::
 Opt MeasConfigMN__Type MeasConfigMN__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MRDC_AssistanceInfo__Type MRDC_AssistanceInfo__cond ::
 Opt CG_ConfigInfo_v1540_IEs__Type CG_ConfigInfo_v1540_IEs__cond ::
 nil).
Definition CG_ConfigInfo_IEs__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_IEs__ue_CapabilityInfo z) /\
  opt_cond MeasResultList2NR__cond (CG_ConfigInfo_IEs__candidateCellInfoListMN z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_IEs__candidateCellInfoListSN z) /\
  opt_cond MeasResultCellListSFTD_NR__cond (CG_ConfigInfo_IEs__measResultCellListSFTD_NR z) /\
  opt_cond CG_ConfigInfo_IEs__scgFailureInfo__cond (CG_ConfigInfo_IEs__scgFailureInfo z) /\
  opt_cond ConfigRestrictInfoSCG__cond (CG_ConfigInfo_IEs__configRestrictInfo z) /\
  opt_cond DRX_Info__cond (CG_ConfigInfo_IEs__drx_InfoMCG z) /\
  opt_cond MeasConfigMN__cond (CG_ConfigInfo_IEs__measConfigMN z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_IEs__sourceConfigSCG z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_IEs__scg_RB_Config z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_IEs__mcg_RB_Config z) /\
  opt_cond MRDC_AssistanceInfo__cond (CG_ConfigInfo_IEs__mrdc_AssistanceInfo z) /\
  opt_cond CG_ConfigInfo_v1540_IEs__cond (CG_ConfigInfo_IEs__nonCriticalExtension z) /\
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
Definition CG_ConfigInfo_IEs__scgFailureInfo__failureType__Format : T_Format CG_ConfigInfo_IEs__scgFailureInfo__failureType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_ConfigInfo_IEs__scgFailureInfo__failureType__nat__Format CG_ConfigInfo_IEs__scgFailureInfo__failureType__F1 CG_ConfigInfo_IEs__scgFailureInfo__failureType__F2 CG_ConfigInfo_IEs__scgFailureInfo__failureType__F1F2 CG_ConfigInfo_IEs__scgFailureInfo__failureType__F2F1.

Opaque CG_ConfigInfo_IEs__scgFailureInfo__failureType__cond CG_ConfigInfo_IEs__scgFailureInfo__failureType__Format.


Definition CG_ConfigInfo_IEs__scgFailureInfo__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_IEs__scgFailureInfo__list.
Definition CG_ConfigInfo_IEs__scgFailureInfo__Format_list : CG_ConfigInfo_IEs__scgFailureInfo__Format_Type :=
  (CG_ConfigInfo_IEs__scgFailureInfo__failureType__Format, (octet_string_nc__Format, unit_format)).
Definition CG_ConfigInfo_IEs__scgFailureInfo__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_IEs__scgFailureInfo__list CG_ConfigInfo_IEs__scgFailureInfo__Format_list.
Definition CG_ConfigInfo_IEs__scgFailureInfo__F1 z :=
  (CG_ConfigInfo_IEs__scgFailureInfo__failureType z, (CG_ConfigInfo_IEs__scgFailureInfo__measResultSCG z, tt)).
Definition CG_ConfigInfo_IEs__scgFailureInfo__F2 (y : seq_type CG_ConfigInfo_IEs__scgFailureInfo__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CG_ConfigInfo_IEs__scgFailureInfo__Type i0 i1
  end.
Lemma CG_ConfigInfo_IEs__scgFailureInfo__F1F2_cond (z : CG_ConfigInfo_IEs__scgFailureInfo__Type)
  : CG_ConfigInfo_IEs__scgFailureInfo__cond z ->
  (seq_cond CG_ConfigInfo_IEs__scgFailureInfo__list (CG_ConfigInfo_IEs__scgFailureInfo__F1 z)).
intro H. unfold CG_ConfigInfo_IEs__scgFailureInfo__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_IEs__scgFailureInfo__F1F2_cond2 (z : CG_ConfigInfo_IEs__scgFailureInfo__Type)
 : CG_ConfigInfo_IEs__scgFailureInfo__F2 (CG_ConfigInfo_IEs__scgFailureInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_IEs__scgFailureInfo__F2F1_cond (y : seq_type CG_ConfigInfo_IEs__scgFailureInfo__list)
  : seq_cond CG_ConfigInfo_IEs__scgFailureInfo__list y ->
 (CG_ConfigInfo_IEs__scgFailureInfo__cond (CG_ConfigInfo_IEs__scgFailureInfo__F2 y)) /\  CG_ConfigInfo_IEs__scgFailureInfo__F1 (CG_ConfigInfo_IEs__scgFailureInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_IEs__scgFailureInfo__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_IEs__scgFailureInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_IEs__scgFailureInfo__Format : T_Format CG_ConfigInfo_IEs__scgFailureInfo__Type CG_ConfigInfo_IEs__scgFailureInfo__cond :=
        proj2_format  CG_ConfigInfo_IEs__scgFailureInfo__cond CG_ConfigInfo_IEs__scgFailureInfo__list__Format
    CG_ConfigInfo_IEs__scgFailureInfo__F1 CG_ConfigInfo_IEs__scgFailureInfo__F2 CG_ConfigInfo_IEs__scgFailureInfo__F1F2_cond  CG_ConfigInfo_IEs__scgFailureInfo__F1F2_cond2 CG_ConfigInfo_IEs__scgFailureInfo__F2F1_cond.
Opaque CG_ConfigInfo_IEs__scgFailureInfo__cond CG_ConfigInfo_IEs__scgFailureInfo__Format.


Definition CG_ConfigInfo_IEs__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_IEs__list.
Definition CG_ConfigInfo_IEs__Format_list : CG_ConfigInfo_IEs__Format_Type :=
  (octet_string_nc__Format, (MeasResultList2NR__Format, (octet_string_nc__Format, (MeasResultCellListSFTD_NR__Format, (CG_ConfigInfo_IEs__scgFailureInfo__Format, (ConfigRestrictInfoSCG__Format, (DRX_Info__Format, (MeasConfigMN__Format, (octet_string_nc__Format, (octet_string_nc__Format, (octet_string_nc__Format, (MRDC_AssistanceInfo__Format, (CG_ConfigInfo_v1540_IEs__Format, unit_format))))))))))))).
Definition CG_ConfigInfo_IEs__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_IEs__list CG_ConfigInfo_IEs__Format_list.
Definition CG_ConfigInfo_IEs__F1 z :=
  (CG_ConfigInfo_IEs__ue_CapabilityInfo z, (CG_ConfigInfo_IEs__candidateCellInfoListMN z, (CG_ConfigInfo_IEs__candidateCellInfoListSN z, (CG_ConfigInfo_IEs__measResultCellListSFTD_NR z, (CG_ConfigInfo_IEs__scgFailureInfo z, (CG_ConfigInfo_IEs__configRestrictInfo z, (CG_ConfigInfo_IEs__drx_InfoMCG z, (CG_ConfigInfo_IEs__measConfigMN z, (CG_ConfigInfo_IEs__sourceConfigSCG z, (CG_ConfigInfo_IEs__scg_RB_Config z, (CG_ConfigInfo_IEs__mcg_RB_Config z, (CG_ConfigInfo_IEs__mrdc_AssistanceInfo z, (CG_ConfigInfo_IEs__nonCriticalExtension z, tt))))))))))))).
Definition CG_ConfigInfo_IEs__F2 (y : seq_type CG_ConfigInfo_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, _)))))))))))))=>
    make__CG_ConfigInfo_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12
  end.
Lemma CG_ConfigInfo_IEs__F1F2_cond (z : CG_ConfigInfo_IEs__Type)
  : CG_ConfigInfo_IEs__cond z ->
  (seq_cond CG_ConfigInfo_IEs__list (CG_ConfigInfo_IEs__F1 z)).
intro H. unfold CG_ConfigInfo_IEs__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_IEs__F1F2_cond2 (z : CG_ConfigInfo_IEs__Type)
 : CG_ConfigInfo_IEs__F2 (CG_ConfigInfo_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_IEs__F2F1_cond (y : seq_type CG_ConfigInfo_IEs__list)
  : seq_cond CG_ConfigInfo_IEs__list y ->
 (CG_ConfigInfo_IEs__cond (CG_ConfigInfo_IEs__F2 y)) /\  CG_ConfigInfo_IEs__F1 (CG_ConfigInfo_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_IEs__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_IEs__Format : T_Format CG_ConfigInfo_IEs__Type CG_ConfigInfo_IEs__cond :=
        proj2_format  CG_ConfigInfo_IEs__cond CG_ConfigInfo_IEs__list__Format
    CG_ConfigInfo_IEs__F1 CG_ConfigInfo_IEs__F2 CG_ConfigInfo_IEs__F1F2_cond  CG_ConfigInfo_IEs__F1F2_cond2 CG_ConfigInfo_IEs__F2F1_cond.
Opaque CG_ConfigInfo_IEs__cond CG_ConfigInfo_IEs__Format.

