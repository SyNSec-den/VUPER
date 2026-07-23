Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Inductive CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Type : Set :=
 | CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__t313_Expiry
 | CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__randomAccessProblem
 | CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__rlc_MaxNumRetx
 | CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__scg_ChangeFailure
.
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__cond := (fun (_ : CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Type) => True).
Lemma CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__nat__helper.

Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F1 t :=
  match t with
  | CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__t313_Expiry => 0
  | CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__randomAccessProblem => 1
  | CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__rlc_MaxNumRetx => 2
  | CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__scg_ChangeFailure => 3
  end.
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F2 n :=
  match n with
  | 0 => CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__t313_Expiry
  | 1 => CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__randomAccessProblem
  | 2 => CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__rlc_MaxNumRetx
  | 3 => CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__scg_ChangeFailure
  | _ => CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__t313_Expiry
  end.
Lemma CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F1F2 : forall x : CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Type, (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F1 x <= 3) /\ CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F2 (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F1 x) = x. imp_solve. Qed.
Lemma CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F2F1 : forall (y : nat) (H : y <= 3), CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F1 (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F2 y) = y. enum_solve H y. Qed.

Record CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Type : Set :=
  make__CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Type {
    CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA : CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Type ;
    CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__measResultSCG_EUTRA : octet_string ;
}.
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list := (
 Nor CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Type CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond z := 
  CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__cond (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__measResultSCG_EUTRA z) /\
  True.

Require Import NR.DRX_Config.

Opaque DRX_Config__cond DRX_Config__Format.

Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Require Import NR.CGI_InfoEUTRA.

Opaque CGI_InfoEUTRA__cond CGI_InfoEUTRA__Format.

Record CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Type : Set :=
  make__CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Type {
    CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__eutraFrequency : ARFCN_ValueEUTRA__Type ;
    CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cellForWhichToReportCGI_EUTRA : EUTRA_PhysCellId__Type ;
    CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cgi_InfoEUTRA : CGI_InfoEUTRA__Type ;
}.
Definition CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Nor EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
 Nor CGI_InfoEUTRA__Type CGI_InfoEUTRA__cond ::
 nil).
Definition CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond z := 
  ARFCN_ValueEUTRA__cond (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__eutraFrequency z) /\
  EUTRA_PhysCellId__cond (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cellForWhichToReportCGI_EUTRA z) /\
  CGI_InfoEUTRA__cond (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cgi_InfoEUTRA z) /\
  True.

Require Import NR.MeasResultCellListSFTD_EUTRA.

Opaque MeasResultCellListSFTD_EUTRA__cond MeasResultCellListSFTD_EUTRA__Format.

Require Import NR.FR_InfoList.

Opaque FR_InfoList__cond FR_InfoList__Format.

Require Import NR.CG_ConfigInfo_v1570_IEs.

Opaque CG_ConfigInfo_v1570_IEs__cond CG_ConfigInfo_v1570_IEs__Format.

Record CG_ConfigInfo_v1560_IEs__Type : Set :=
  make__CG_ConfigInfo_v1560_IEs__Type {
    CG_ConfigInfo_v1560_IEs__candidateCellInfoListMN_EUTRA : option octet_string ;
    CG_ConfigInfo_v1560_IEs__candidateCellInfoListSN_EUTRA : option octet_string ;
    CG_ConfigInfo_v1560_IEs__sourceConfigSCG_EUTRA : option octet_string ;
    CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA : option CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Type ;
    CG_ConfigInfo_v1560_IEs__drx_ConfigMCG : option DRX_Config__Type ;
    CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA : option CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Type ;
    CG_ConfigInfo_v1560_IEs__measResultCellListSFTD_EUTRA : option MeasResultCellListSFTD_EUTRA__Type ;
    CG_ConfigInfo_v1560_IEs__fr_InfoListMCG : option FR_InfoList__Type ;
    CG_ConfigInfo_v1560_IEs__nonCriticalExtension : option CG_ConfigInfo_v1570_IEs__Type ;
}.
Definition CG_ConfigInfo_v1560_IEs__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Type CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond ::
 Opt DRX_Config__Type DRX_Config__cond ::
 Opt CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Type CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond ::
 Opt MeasResultCellListSFTD_EUTRA__Type MeasResultCellListSFTD_EUTRA__cond ::
 Opt FR_InfoList__Type FR_InfoList__cond ::
 Opt CG_ConfigInfo_v1570_IEs__Type CG_ConfigInfo_v1570_IEs__cond ::
 nil).
Definition CG_ConfigInfo_v1560_IEs__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_v1560_IEs__candidateCellInfoListMN_EUTRA z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_v1560_IEs__candidateCellInfoListSN_EUTRA z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_ConfigInfo_v1560_IEs__sourceConfigSCG_EUTRA z) /\
  opt_cond CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA z) /\
  opt_cond DRX_Config__cond (CG_ConfigInfo_v1560_IEs__drx_ConfigMCG z) /\
  opt_cond CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA z) /\
  opt_cond MeasResultCellListSFTD_EUTRA__cond (CG_ConfigInfo_v1560_IEs__measResultCellListSFTD_EUTRA z) /\
  opt_cond FR_InfoList__cond (CG_ConfigInfo_v1560_IEs__fr_InfoListMCG z) /\
  opt_cond CG_ConfigInfo_v1570_IEs__cond (CG_ConfigInfo_v1560_IEs__nonCriticalExtension z) /\
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
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Format : T_Format CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__nat__Format CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F1 CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F2 CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F1F2 CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__F2F1.

Opaque CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__cond CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Format.


Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list.
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Format_list : CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Format_Type :=
  (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA__Format, (octet_string_nc__Format, unit_format)).
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Format_list.
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1 z :=
  (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__failureTypeEUTRA z, (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__measResultSCG_EUTRA z, tt)).
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F2 (y : seq_type CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Type i0 i1
  end.
Lemma CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1F2_cond (z : CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Type)
  : CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond z ->
  (seq_cond CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1 z)).
intro H. unfold CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1F2_cond2 (z : CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Type)
 : CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F2 (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F2F1_cond (y : seq_type CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list)
  : seq_cond CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list y ->
 (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F2 y)) /\  CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1 (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Format : T_Format CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Type CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond :=
        proj2_format  CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__list__Format
    CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1 CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F2 CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1F2_cond  CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F1F2_cond2 CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__F2F1_cond.
Opaque CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__cond CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Format.


Definition CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list.
Definition CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Format_list : CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Format_Type :=
  (ARFCN_ValueEUTRA__Format, (EUTRA_PhysCellId__Format, (CGI_InfoEUTRA__Format, unit_format))).
Definition CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Format_list.
Definition CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1 z :=
  (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__eutraFrequency z, (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cellForWhichToReportCGI_EUTRA z, (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cgi_InfoEUTRA z, tt))).
Definition CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F2 (y : seq_type CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Type i0 i1 i2
  end.
Lemma CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1F2_cond (z : CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Type)
  : CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond z ->
  (seq_cond CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1 z)).
intro H. unfold CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1F2_cond2 (z : CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Type)
 : CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F2 (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F2F1_cond (y : seq_type CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list)
  : seq_cond CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list y ->
 (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F2 y)) /\  CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1 (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Format : T_Format CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Type CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond :=
        proj2_format  CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__list__Format
    CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1 CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F2 CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1F2_cond  CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F1F2_cond2 CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__F2F1_cond.
Opaque CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__cond CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Format.


Definition CG_ConfigInfo_v1560_IEs__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_v1560_IEs__list.
Definition CG_ConfigInfo_v1560_IEs__Format_list : CG_ConfigInfo_v1560_IEs__Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, (octet_string_nc__Format, (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA__Format, (DRX_Config__Format, (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA__Format, (MeasResultCellListSFTD_EUTRA__Format, (FR_InfoList__Format, (CG_ConfigInfo_v1570_IEs__Format, unit_format))))))))).
Definition CG_ConfigInfo_v1560_IEs__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_v1560_IEs__list CG_ConfigInfo_v1560_IEs__Format_list.
Definition CG_ConfigInfo_v1560_IEs__F1 z :=
  (CG_ConfigInfo_v1560_IEs__candidateCellInfoListMN_EUTRA z, (CG_ConfigInfo_v1560_IEs__candidateCellInfoListSN_EUTRA z, (CG_ConfigInfo_v1560_IEs__sourceConfigSCG_EUTRA z, (CG_ConfigInfo_v1560_IEs__scgFailureInfoEUTRA z, (CG_ConfigInfo_v1560_IEs__drx_ConfigMCG z, (CG_ConfigInfo_v1560_IEs__measResultReportCGI_EUTRA z, (CG_ConfigInfo_v1560_IEs__measResultCellListSFTD_EUTRA z, (CG_ConfigInfo_v1560_IEs__fr_InfoListMCG z, (CG_ConfigInfo_v1560_IEs__nonCriticalExtension z, tt))))))))).
Definition CG_ConfigInfo_v1560_IEs__F2 (y : seq_type CG_ConfigInfo_v1560_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _)))))))))=>
    make__CG_ConfigInfo_v1560_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Lemma CG_ConfigInfo_v1560_IEs__F1F2_cond (z : CG_ConfigInfo_v1560_IEs__Type)
  : CG_ConfigInfo_v1560_IEs__cond z ->
  (seq_cond CG_ConfigInfo_v1560_IEs__list (CG_ConfigInfo_v1560_IEs__F1 z)).
intro H. unfold CG_ConfigInfo_v1560_IEs__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1560_IEs__F1F2_cond2 (z : CG_ConfigInfo_v1560_IEs__Type)
 : CG_ConfigInfo_v1560_IEs__F2 (CG_ConfigInfo_v1560_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1560_IEs__F2F1_cond (y : seq_type CG_ConfigInfo_v1560_IEs__list)
  : seq_cond CG_ConfigInfo_v1560_IEs__list y ->
 (CG_ConfigInfo_v1560_IEs__cond (CG_ConfigInfo_v1560_IEs__F2 y)) /\  CG_ConfigInfo_v1560_IEs__F1 (CG_ConfigInfo_v1560_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_v1560_IEs__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_v1560_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_v1560_IEs__Format : T_Format CG_ConfigInfo_v1560_IEs__Type CG_ConfigInfo_v1560_IEs__cond :=
        proj2_format  CG_ConfigInfo_v1560_IEs__cond CG_ConfigInfo_v1560_IEs__list__Format
    CG_ConfigInfo_v1560_IEs__F1 CG_ConfigInfo_v1560_IEs__F2 CG_ConfigInfo_v1560_IEs__F1F2_cond  CG_ConfigInfo_v1560_IEs__F1F2_cond2 CG_ConfigInfo_v1560_IEs__F2F1_cond.
Opaque CG_ConfigInfo_v1560_IEs__cond CG_ConfigInfo_v1560_IEs__Format.

