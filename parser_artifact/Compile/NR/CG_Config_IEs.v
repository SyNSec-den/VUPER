Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.ConfigRestrictModReqSCG.

Opaque ConfigRestrictModReqSCG__cond ConfigRestrictModReqSCG__Format.

Require Import NR.DRX_Info.

Opaque DRX_Info__cond DRX_Info__Format.

Require Import NR.MeasConfigSN.

Opaque MeasConfigSN__cond MeasConfigSN__Format.

Require Import NR.BandCombinationInfoSN.

Opaque BandCombinationInfoSN__cond BandCombinationInfoSN__Format.

Require Import NR.FR_InfoList.

Opaque FR_InfoList__cond FR_InfoList__Format.

Require Import NR.CandidateServingFreqListNR.

Opaque CandidateServingFreqListNR__cond CandidateServingFreqListNR__Format.

Require Import NR.CG_Config_v1540_IEs.

Opaque CG_Config_v1540_IEs__cond CG_Config_v1540_IEs__Format.

Record CG_Config_IEs__Type : Set :=
  make__CG_Config_IEs__Type {
    CG_Config_IEs__scg_CellGroupConfig : option octet_string ;
    CG_Config_IEs__scg_RB_Config : option octet_string ;
    CG_Config_IEs__configRestrictModReq : option ConfigRestrictModReqSCG__Type ;
    CG_Config_IEs__drx_InfoSCG : option DRX_Info__Type ;
    CG_Config_IEs__candidateCellInfoListSN : option octet_string ;
    CG_Config_IEs__measConfigSN : option MeasConfigSN__Type ;
    CG_Config_IEs__selectedBandCombination : option BandCombinationInfoSN__Type ;
    CG_Config_IEs__fr_InfoListSCG : option FR_InfoList__Type ;
    CG_Config_IEs__candidateServingFreqListNR : option CandidateServingFreqListNR__Type ;
    CG_Config_IEs__nonCriticalExtension : option CG_Config_v1540_IEs__Type ;
}.
Definition CG_Config_IEs__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt ConfigRestrictModReqSCG__Type ConfigRestrictModReqSCG__cond ::
 Opt DRX_Info__Type DRX_Info__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MeasConfigSN__Type MeasConfigSN__cond ::
 Opt BandCombinationInfoSN__Type BandCombinationInfoSN__cond ::
 Opt FR_InfoList__Type FR_InfoList__cond ::
 Opt CandidateServingFreqListNR__Type CandidateServingFreqListNR__cond ::
 Opt CG_Config_v1540_IEs__Type CG_Config_v1540_IEs__cond ::
 nil).
Definition CG_Config_IEs__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_Config_IEs__scg_CellGroupConfig z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_Config_IEs__scg_RB_Config z) /\
  opt_cond ConfigRestrictModReqSCG__cond (CG_Config_IEs__configRestrictModReq z) /\
  opt_cond DRX_Info__cond (CG_Config_IEs__drx_InfoSCG z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_Config_IEs__candidateCellInfoListSN z) /\
  opt_cond MeasConfigSN__cond (CG_Config_IEs__measConfigSN z) /\
  opt_cond BandCombinationInfoSN__cond (CG_Config_IEs__selectedBandCombination z) /\
  opt_cond FR_InfoList__cond (CG_Config_IEs__fr_InfoListSCG z) /\
  opt_cond CandidateServingFreqListNR__cond (CG_Config_IEs__candidateServingFreqListNR z) /\
  opt_cond CG_Config_v1540_IEs__cond (CG_Config_IEs__nonCriticalExtension z) /\
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

Definition CG_Config_IEs__Format_Type := Eval cbn in seq_format_prod CG_Config_IEs__list.
Definition CG_Config_IEs__Format_list : CG_Config_IEs__Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, (ConfigRestrictModReqSCG__Format, (DRX_Info__Format, (octet_string_nc__Format, (MeasConfigSN__Format, (BandCombinationInfoSN__Format, (FR_InfoList__Format, (CandidateServingFreqListNR__Format, (CG_Config_v1540_IEs__Format, unit_format)))))))))).
Definition CG_Config_IEs__list__Format := (*Eval compute in *) seq_format CG_Config_IEs__list CG_Config_IEs__Format_list.
Definition CG_Config_IEs__F1 z :=
  (CG_Config_IEs__scg_CellGroupConfig z, (CG_Config_IEs__scg_RB_Config z, (CG_Config_IEs__configRestrictModReq z, (CG_Config_IEs__drx_InfoSCG z, (CG_Config_IEs__candidateCellInfoListSN z, (CG_Config_IEs__measConfigSN z, (CG_Config_IEs__selectedBandCombination z, (CG_Config_IEs__fr_InfoListSCG z, (CG_Config_IEs__candidateServingFreqListNR z, (CG_Config_IEs__nonCriticalExtension z, tt)))))))))).
Definition CG_Config_IEs__F2 (y : seq_type CG_Config_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__CG_Config_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma CG_Config_IEs__F1F2_cond (z : CG_Config_IEs__Type)
  : CG_Config_IEs__cond z ->
  (seq_cond CG_Config_IEs__list (CG_Config_IEs__F1 z)).
intro H. unfold CG_Config_IEs__cond in H. simpl. auto. Qed.
Lemma CG_Config_IEs__F1F2_cond2 (z : CG_Config_IEs__Type)
 : CG_Config_IEs__F2 (CG_Config_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_Config_IEs__F2F1_cond (y : seq_type CG_Config_IEs__list)
  : seq_cond CG_Config_IEs__list y ->
 (CG_Config_IEs__cond (CG_Config_IEs__F2 y)) /\  CG_Config_IEs__F1 (CG_Config_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_Config_IEs__cond. simpl in *. auto.
 - simpl. unfold CG_Config_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_Config_IEs__Format : T_Format CG_Config_IEs__Type CG_Config_IEs__cond :=
        proj2_format  CG_Config_IEs__cond CG_Config_IEs__list__Format
    CG_Config_IEs__F1 CG_Config_IEs__F2 CG_Config_IEs__F1F2_cond  CG_Config_IEs__F1F2_cond2 CG_Config_IEs__F2F1_cond.
Opaque CG_Config_IEs__cond CG_Config_IEs__Format.

