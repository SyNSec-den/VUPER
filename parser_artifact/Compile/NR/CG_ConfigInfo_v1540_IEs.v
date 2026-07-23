Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.PH_TypeListMCG.

Opaque PH_TypeListMCG__cond PH_TypeListMCG__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.CGI_InfoNR.

Opaque CGI_InfoNR__cond CGI_InfoNR__Format.

Record CG_ConfigInfo_v1540_IEs__measResultReportCGI__Type : Set :=
  make__CG_ConfigInfo_v1540_IEs__measResultReportCGI__Type {
    CG_ConfigInfo_v1540_IEs__measResultReportCGI__ssbFrequency : ARFCN_ValueNR__Type ;
    CG_ConfigInfo_v1540_IEs__measResultReportCGI__cellForWhichToReportCGI : PhysCellId__Type ;
    CG_ConfigInfo_v1540_IEs__measResultReportCGI__cgi_Info : CGI_InfoNR__Type ;
}.
Definition CG_ConfigInfo_v1540_IEs__measResultReportCGI__list := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor CGI_InfoNR__Type CGI_InfoNR__cond ::
 nil).
Definition CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond z := 
  ARFCN_ValueNR__cond (CG_ConfigInfo_v1540_IEs__measResultReportCGI__ssbFrequency z) /\
  PhysCellId__cond (CG_ConfigInfo_v1540_IEs__measResultReportCGI__cellForWhichToReportCGI z) /\
  CGI_InfoNR__cond (CG_ConfigInfo_v1540_IEs__measResultReportCGI__cgi_Info z) /\
  True.

Require Import NR.CG_ConfigInfo_v1560_IEs.

Opaque CG_ConfigInfo_v1560_IEs__cond CG_ConfigInfo_v1560_IEs__Format.

Record CG_ConfigInfo_v1540_IEs__Type : Set :=
  make__CG_ConfigInfo_v1540_IEs__Type {
    CG_ConfigInfo_v1540_IEs__ph_InfoMCG : option PH_TypeListMCG__Type ;
    CG_ConfigInfo_v1540_IEs__measResultReportCGI : option CG_ConfigInfo_v1540_IEs__measResultReportCGI__Type ;
    CG_ConfigInfo_v1540_IEs__nonCriticalExtension : option CG_ConfigInfo_v1560_IEs__Type ;
}.
Definition CG_ConfigInfo_v1540_IEs__list := (
 Opt PH_TypeListMCG__Type PH_TypeListMCG__cond ::
 Opt CG_ConfigInfo_v1540_IEs__measResultReportCGI__Type CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond ::
 Opt CG_ConfigInfo_v1560_IEs__Type CG_ConfigInfo_v1560_IEs__cond ::
 nil).
Definition CG_ConfigInfo_v1540_IEs__cond z := 
  opt_cond PH_TypeListMCG__cond (CG_ConfigInfo_v1540_IEs__ph_InfoMCG z) /\
  opt_cond CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond (CG_ConfigInfo_v1540_IEs__measResultReportCGI z) /\
  opt_cond CG_ConfigInfo_v1560_IEs__cond (CG_ConfigInfo_v1540_IEs__nonCriticalExtension z) /\
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

Definition CG_ConfigInfo_v1540_IEs__measResultReportCGI__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_v1540_IEs__measResultReportCGI__list.
Definition CG_ConfigInfo_v1540_IEs__measResultReportCGI__Format_list : CG_ConfigInfo_v1540_IEs__measResultReportCGI__Format_Type :=
  (ARFCN_ValueNR__Format, (PhysCellId__Format, (CGI_InfoNR__Format, unit_format))).
Definition CG_ConfigInfo_v1540_IEs__measResultReportCGI__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_v1540_IEs__measResultReportCGI__list CG_ConfigInfo_v1540_IEs__measResultReportCGI__Format_list.
Definition CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1 z :=
  (CG_ConfigInfo_v1540_IEs__measResultReportCGI__ssbFrequency z, (CG_ConfigInfo_v1540_IEs__measResultReportCGI__cellForWhichToReportCGI z, (CG_ConfigInfo_v1540_IEs__measResultReportCGI__cgi_Info z, tt))).
Definition CG_ConfigInfo_v1540_IEs__measResultReportCGI__F2 (y : seq_type CG_ConfigInfo_v1540_IEs__measResultReportCGI__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CG_ConfigInfo_v1540_IEs__measResultReportCGI__Type i0 i1 i2
  end.
Lemma CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1F2_cond (z : CG_ConfigInfo_v1540_IEs__measResultReportCGI__Type)
  : CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond z ->
  (seq_cond CG_ConfigInfo_v1540_IEs__measResultReportCGI__list (CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1 z)).
intro H. unfold CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1F2_cond2 (z : CG_ConfigInfo_v1540_IEs__measResultReportCGI__Type)
 : CG_ConfigInfo_v1540_IEs__measResultReportCGI__F2 (CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1540_IEs__measResultReportCGI__F2F1_cond (y : seq_type CG_ConfigInfo_v1540_IEs__measResultReportCGI__list)
  : seq_cond CG_ConfigInfo_v1540_IEs__measResultReportCGI__list y ->
 (CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond (CG_ConfigInfo_v1540_IEs__measResultReportCGI__F2 y)) /\  CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1 (CG_ConfigInfo_v1540_IEs__measResultReportCGI__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_v1540_IEs__measResultReportCGI__Format : T_Format CG_ConfigInfo_v1540_IEs__measResultReportCGI__Type CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond :=
        proj2_format  CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond CG_ConfigInfo_v1540_IEs__measResultReportCGI__list__Format
    CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1 CG_ConfigInfo_v1540_IEs__measResultReportCGI__F2 CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1F2_cond  CG_ConfigInfo_v1540_IEs__measResultReportCGI__F1F2_cond2 CG_ConfigInfo_v1540_IEs__measResultReportCGI__F2F1_cond.
Opaque CG_ConfigInfo_v1540_IEs__measResultReportCGI__cond CG_ConfigInfo_v1540_IEs__measResultReportCGI__Format.


Definition CG_ConfigInfo_v1540_IEs__Format_Type := Eval cbn in seq_format_prod CG_ConfigInfo_v1540_IEs__list.
Definition CG_ConfigInfo_v1540_IEs__Format_list : CG_ConfigInfo_v1540_IEs__Format_Type :=
  (PH_TypeListMCG__Format, (CG_ConfigInfo_v1540_IEs__measResultReportCGI__Format, (CG_ConfigInfo_v1560_IEs__Format, unit_format))).
Definition CG_ConfigInfo_v1540_IEs__list__Format := (*Eval compute in *) seq_format CG_ConfigInfo_v1540_IEs__list CG_ConfigInfo_v1540_IEs__Format_list.
Definition CG_ConfigInfo_v1540_IEs__F1 z :=
  (CG_ConfigInfo_v1540_IEs__ph_InfoMCG z, (CG_ConfigInfo_v1540_IEs__measResultReportCGI z, (CG_ConfigInfo_v1540_IEs__nonCriticalExtension z, tt))).
Definition CG_ConfigInfo_v1540_IEs__F2 (y : seq_type CG_ConfigInfo_v1540_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CG_ConfigInfo_v1540_IEs__Type i0 i1 i2
  end.
Lemma CG_ConfigInfo_v1540_IEs__F1F2_cond (z : CG_ConfigInfo_v1540_IEs__Type)
  : CG_ConfigInfo_v1540_IEs__cond z ->
  (seq_cond CG_ConfigInfo_v1540_IEs__list (CG_ConfigInfo_v1540_IEs__F1 z)).
intro H. unfold CG_ConfigInfo_v1540_IEs__cond in H. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1540_IEs__F1F2_cond2 (z : CG_ConfigInfo_v1540_IEs__Type)
 : CG_ConfigInfo_v1540_IEs__F2 (CG_ConfigInfo_v1540_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_ConfigInfo_v1540_IEs__F2F1_cond (y : seq_type CG_ConfigInfo_v1540_IEs__list)
  : seq_cond CG_ConfigInfo_v1540_IEs__list y ->
 (CG_ConfigInfo_v1540_IEs__cond (CG_ConfigInfo_v1540_IEs__F2 y)) /\  CG_ConfigInfo_v1540_IEs__F1 (CG_ConfigInfo_v1540_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_ConfigInfo_v1540_IEs__cond. simpl in *. auto.
 - simpl. unfold CG_ConfigInfo_v1540_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_ConfigInfo_v1540_IEs__Format : T_Format CG_ConfigInfo_v1540_IEs__Type CG_ConfigInfo_v1540_IEs__cond :=
        proj2_format  CG_ConfigInfo_v1540_IEs__cond CG_ConfigInfo_v1540_IEs__list__Format
    CG_ConfigInfo_v1540_IEs__F1 CG_ConfigInfo_v1540_IEs__F2 CG_ConfigInfo_v1540_IEs__F1F2_cond  CG_ConfigInfo_v1540_IEs__F1F2_cond2 CG_ConfigInfo_v1540_IEs__F2F1_cond.
Opaque CG_ConfigInfo_v1540_IEs__cond CG_ConfigInfo_v1540_IEs__Format.

