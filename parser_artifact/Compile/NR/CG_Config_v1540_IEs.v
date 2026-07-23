Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Record CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Type : Set :=
  make__CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Type {
    CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__ssbFrequency : ARFCN_ValueNR__Type ;
    CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cellForWhichToReportCGI : PhysCellId__Type ;
}.
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor PhysCellId__Type PhysCellId__cond ::
 nil).
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond z := 
  ARFCN_ValueNR__cond (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__ssbFrequency z) /\
  PhysCellId__cond (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cellForWhichToReportCGI z) /\
  True.

Record CG_Config_v1540_IEs__reportCGI_RequestNR__Type : Set :=
  make__CG_Config_v1540_IEs__reportCGI_RequestNR__Type {
    CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo : option CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Type ;
}.
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__list := (
 Opt CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Type CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond ::
 nil).
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__cond z := 
  opt_cond CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo z) /\
  True.

Require Import NR.PH_TypeListSCG.

Opaque PH_TypeListSCG__cond PH_TypeListSCG__Format.

Require Import NR.CG_Config_v1560_IEs.

Opaque CG_Config_v1560_IEs__cond CG_Config_v1560_IEs__Format.

Record CG_Config_v1540_IEs__Type : Set :=
  make__CG_Config_v1540_IEs__Type {
    CG_Config_v1540_IEs__pSCellFrequency : option ARFCN_ValueNR__Type ;
    CG_Config_v1540_IEs__reportCGI_RequestNR : option CG_Config_v1540_IEs__reportCGI_RequestNR__Type ;
    CG_Config_v1540_IEs__ph_InfoSCG : option PH_TypeListSCG__Type ;
    CG_Config_v1540_IEs__nonCriticalExtension : option CG_Config_v1560_IEs__Type ;
}.
Definition CG_Config_v1540_IEs__list := (
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt CG_Config_v1540_IEs__reportCGI_RequestNR__Type CG_Config_v1540_IEs__reportCGI_RequestNR__cond ::
 Opt PH_TypeListSCG__Type PH_TypeListSCG__cond ::
 Opt CG_Config_v1560_IEs__Type CG_Config_v1560_IEs__cond ::
 nil).
Definition CG_Config_v1540_IEs__cond z := 
  opt_cond ARFCN_ValueNR__cond (CG_Config_v1540_IEs__pSCellFrequency z) /\
  opt_cond CG_Config_v1540_IEs__reportCGI_RequestNR__cond (CG_Config_v1540_IEs__reportCGI_RequestNR z) /\
  opt_cond PH_TypeListSCG__cond (CG_Config_v1540_IEs__ph_InfoSCG z) /\
  opt_cond CG_Config_v1560_IEs__cond (CG_Config_v1540_IEs__nonCriticalExtension z) /\
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

Definition CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Format_Type := Eval cbn in seq_format_prod CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list.
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Format_list : CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Format_Type :=
  (ARFCN_ValueNR__Format, (PhysCellId__Format, unit_format)).
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list__Format := (*Eval compute in *) seq_format CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Format_list.
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1 z :=
  (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__ssbFrequency z, (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cellForWhichToReportCGI z, tt)).
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F2 (y : seq_type CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Type i0 i1
  end.
Lemma CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1F2_cond (z : CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Type)
  : CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond z ->
  (seq_cond CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1 z)).
intro H. unfold CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond in H. simpl. auto. Qed.
Lemma CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1F2_cond2 (z : CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Type)
 : CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F2 (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F2F1_cond (y : seq_type CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list)
  : seq_cond CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list y ->
 (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F2 y)) /\  CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1 (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond. simpl in *. auto.
 - simpl. unfold CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Format : T_Format CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Type CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond :=
        proj2_format  CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__list__Format
    CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1 CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F2 CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1F2_cond  CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F1F2_cond2 CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__F2F1_cond.
Opaque CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__cond CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Format.


Definition CG_Config_v1540_IEs__reportCGI_RequestNR__Format_Type := Eval cbn in seq_format_prod CG_Config_v1540_IEs__reportCGI_RequestNR__list.
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__Format_list : CG_Config_v1540_IEs__reportCGI_RequestNR__Format_Type :=
  (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo__Format, unit_format).
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__list__Format := (*Eval compute in *) seq_format CG_Config_v1540_IEs__reportCGI_RequestNR__list CG_Config_v1540_IEs__reportCGI_RequestNR__Format_list.
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__F1 z :=
  (CG_Config_v1540_IEs__reportCGI_RequestNR__requestedCellInfo z, tt).
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__F2 (y : seq_type CG_Config_v1540_IEs__reportCGI_RequestNR__list) :=
  match y with
  | (i0, _)=>
    make__CG_Config_v1540_IEs__reportCGI_RequestNR__Type i0
  end.
Lemma CG_Config_v1540_IEs__reportCGI_RequestNR__F1F2_cond (z : CG_Config_v1540_IEs__reportCGI_RequestNR__Type)
  : CG_Config_v1540_IEs__reportCGI_RequestNR__cond z ->
  (seq_cond CG_Config_v1540_IEs__reportCGI_RequestNR__list (CG_Config_v1540_IEs__reportCGI_RequestNR__F1 z)).
intro H. unfold CG_Config_v1540_IEs__reportCGI_RequestNR__cond in H. simpl. auto. Qed.
Lemma CG_Config_v1540_IEs__reportCGI_RequestNR__F1F2_cond2 (z : CG_Config_v1540_IEs__reportCGI_RequestNR__Type)
 : CG_Config_v1540_IEs__reportCGI_RequestNR__F2 (CG_Config_v1540_IEs__reportCGI_RequestNR__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_Config_v1540_IEs__reportCGI_RequestNR__F2F1_cond (y : seq_type CG_Config_v1540_IEs__reportCGI_RequestNR__list)
  : seq_cond CG_Config_v1540_IEs__reportCGI_RequestNR__list y ->
 (CG_Config_v1540_IEs__reportCGI_RequestNR__cond (CG_Config_v1540_IEs__reportCGI_RequestNR__F2 y)) /\  CG_Config_v1540_IEs__reportCGI_RequestNR__F1 (CG_Config_v1540_IEs__reportCGI_RequestNR__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_Config_v1540_IEs__reportCGI_RequestNR__cond. simpl in *. auto.
 - simpl. unfold CG_Config_v1540_IEs__reportCGI_RequestNR__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_Config_v1540_IEs__reportCGI_RequestNR__Format : T_Format CG_Config_v1540_IEs__reportCGI_RequestNR__Type CG_Config_v1540_IEs__reportCGI_RequestNR__cond :=
        proj2_format  CG_Config_v1540_IEs__reportCGI_RequestNR__cond CG_Config_v1540_IEs__reportCGI_RequestNR__list__Format
    CG_Config_v1540_IEs__reportCGI_RequestNR__F1 CG_Config_v1540_IEs__reportCGI_RequestNR__F2 CG_Config_v1540_IEs__reportCGI_RequestNR__F1F2_cond  CG_Config_v1540_IEs__reportCGI_RequestNR__F1F2_cond2 CG_Config_v1540_IEs__reportCGI_RequestNR__F2F1_cond.
Opaque CG_Config_v1540_IEs__reportCGI_RequestNR__cond CG_Config_v1540_IEs__reportCGI_RequestNR__Format.


Definition CG_Config_v1540_IEs__Format_Type := Eval cbn in seq_format_prod CG_Config_v1540_IEs__list.
Definition CG_Config_v1540_IEs__Format_list : CG_Config_v1540_IEs__Format_Type :=
  (ARFCN_ValueNR__Format, (CG_Config_v1540_IEs__reportCGI_RequestNR__Format, (PH_TypeListSCG__Format, (CG_Config_v1560_IEs__Format, unit_format)))).
Definition CG_Config_v1540_IEs__list__Format := (*Eval compute in *) seq_format CG_Config_v1540_IEs__list CG_Config_v1540_IEs__Format_list.
Definition CG_Config_v1540_IEs__F1 z :=
  (CG_Config_v1540_IEs__pSCellFrequency z, (CG_Config_v1540_IEs__reportCGI_RequestNR z, (CG_Config_v1540_IEs__ph_InfoSCG z, (CG_Config_v1540_IEs__nonCriticalExtension z, tt)))).
Definition CG_Config_v1540_IEs__F2 (y : seq_type CG_Config_v1540_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CG_Config_v1540_IEs__Type i0 i1 i2 i3
  end.
Lemma CG_Config_v1540_IEs__F1F2_cond (z : CG_Config_v1540_IEs__Type)
  : CG_Config_v1540_IEs__cond z ->
  (seq_cond CG_Config_v1540_IEs__list (CG_Config_v1540_IEs__F1 z)).
intro H. unfold CG_Config_v1540_IEs__cond in H. simpl. auto. Qed.
Lemma CG_Config_v1540_IEs__F1F2_cond2 (z : CG_Config_v1540_IEs__Type)
 : CG_Config_v1540_IEs__F2 (CG_Config_v1540_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_Config_v1540_IEs__F2F1_cond (y : seq_type CG_Config_v1540_IEs__list)
  : seq_cond CG_Config_v1540_IEs__list y ->
 (CG_Config_v1540_IEs__cond (CG_Config_v1540_IEs__F2 y)) /\  CG_Config_v1540_IEs__F1 (CG_Config_v1540_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_Config_v1540_IEs__cond. simpl in *. auto.
 - simpl. unfold CG_Config_v1540_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_Config_v1540_IEs__Format : T_Format CG_Config_v1540_IEs__Type CG_Config_v1540_IEs__cond :=
        proj2_format  CG_Config_v1540_IEs__cond CG_Config_v1540_IEs__list__Format
    CG_Config_v1540_IEs__F1 CG_Config_v1540_IEs__F2 CG_Config_v1540_IEs__F1F2_cond  CG_Config_v1540_IEs__F1F2_cond2 CG_Config_v1540_IEs__F2F1_cond.
Opaque CG_Config_v1540_IEs__cond CG_Config_v1540_IEs__Format.

