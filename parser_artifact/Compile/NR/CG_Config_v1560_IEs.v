Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Require Import NR.CandidateServingFreqListEUTRA.

Opaque CandidateServingFreqListEUTRA__cond CandidateServingFreqListEUTRA__Format.

Inductive CG_Config_v1560_IEs__needForGaps__Type : Set :=
 | CG_Config_v1560_IEs__needForGaps__true
.
Definition CG_Config_v1560_IEs__needForGaps__cond := (fun (_ : CG_Config_v1560_IEs__needForGaps__Type) => True).
Lemma CG_Config_v1560_IEs__needForGaps__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CG_Config_v1560_IEs__needForGaps__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CG_Config_v1560_IEs__needForGaps__nat__helper.

Definition CG_Config_v1560_IEs__needForGaps__F1 t :=
  match t with
  | CG_Config_v1560_IEs__needForGaps__true => 0
  end.
Definition CG_Config_v1560_IEs__needForGaps__F2 n :=
  match n with
  | 0 => CG_Config_v1560_IEs__needForGaps__true
  | _ => CG_Config_v1560_IEs__needForGaps__true
  end.
Lemma CG_Config_v1560_IEs__needForGaps__F1F2 : forall x : CG_Config_v1560_IEs__needForGaps__Type, (CG_Config_v1560_IEs__needForGaps__F1 x <= 0) /\ CG_Config_v1560_IEs__needForGaps__F2 (CG_Config_v1560_IEs__needForGaps__F1 x) = x. imp_solve. Qed.
Lemma CG_Config_v1560_IEs__needForGaps__F2F1 : forall (y : nat) (H : y <= 0), CG_Config_v1560_IEs__needForGaps__F1 (CG_Config_v1560_IEs__needForGaps__F2 y) = y. enum_solve H y. Qed.

Require Import NR.DRX_Config.

Opaque DRX_Config__cond DRX_Config__Format.

Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Record CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Type : Set :=
  make__CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Type {
    CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__eutraFrequency : ARFCN_ValueEUTRA__Type ;
    CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cellForWhichToReportCGI_EUTRA : EUTRA_PhysCellId__Type ;
}.
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Nor EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
 nil).
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond z := 
  ARFCN_ValueEUTRA__cond (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__eutraFrequency z) /\
  EUTRA_PhysCellId__cond (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cellForWhichToReportCGI_EUTRA z) /\
  True.

Record CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Type : Set :=
  make__CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Type {
    CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA : option CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Type ;
}.
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list := (
 Opt CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Type CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond ::
 nil).
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond z := 
  opt_cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA z) /\
  True.

Require Import NR.CG_Config_v1590_IEs.

Opaque CG_Config_v1590_IEs__cond CG_Config_v1590_IEs__Format.

Record CG_Config_v1560_IEs__Type : Set :=
  make__CG_Config_v1560_IEs__Type {
    CG_Config_v1560_IEs__pSCellFrequencyEUTRA : option ARFCN_ValueEUTRA__Type ;
    CG_Config_v1560_IEs__scg_CellGroupConfigEUTRA : option octet_string ;
    CG_Config_v1560_IEs__candidateCellInfoListSN_EUTRA : option octet_string ;
    CG_Config_v1560_IEs__candidateServingFreqListEUTRA : option CandidateServingFreqListEUTRA__Type ;
    CG_Config_v1560_IEs__needForGaps : option CG_Config_v1560_IEs__needForGaps__Type ;
    CG_Config_v1560_IEs__drx_ConfigSCG : option DRX_Config__Type ;
    CG_Config_v1560_IEs__reportCGI_RequestEUTRA : option CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Type ;
    CG_Config_v1560_IEs__nonCriticalExtension : option CG_Config_v1590_IEs__Type ;
}.
Definition CG_Config_v1560_IEs__list := (
 Opt ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt CandidateServingFreqListEUTRA__Type CandidateServingFreqListEUTRA__cond ::
 Opt CG_Config_v1560_IEs__needForGaps__Type CG_Config_v1560_IEs__needForGaps__cond ::
 Opt DRX_Config__Type DRX_Config__cond ::
 Opt CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Type CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond ::
 Opt CG_Config_v1590_IEs__Type CG_Config_v1590_IEs__cond ::
 nil).
Definition CG_Config_v1560_IEs__cond z := 
  opt_cond ARFCN_ValueEUTRA__cond (CG_Config_v1560_IEs__pSCellFrequencyEUTRA z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_Config_v1560_IEs__scg_CellGroupConfigEUTRA z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (CG_Config_v1560_IEs__candidateCellInfoListSN_EUTRA z) /\
  opt_cond CandidateServingFreqListEUTRA__cond (CG_Config_v1560_IEs__candidateServingFreqListEUTRA z) /\
  opt_cond CG_Config_v1560_IEs__needForGaps__cond (CG_Config_v1560_IEs__needForGaps z) /\
  opt_cond DRX_Config__cond (CG_Config_v1560_IEs__drx_ConfigSCG z) /\
  opt_cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond (CG_Config_v1560_IEs__reportCGI_RequestEUTRA z) /\
  opt_cond CG_Config_v1590_IEs__cond (CG_Config_v1560_IEs__nonCriticalExtension z) /\
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
Definition CG_Config_v1560_IEs__needForGaps__Format : T_Format CG_Config_v1560_IEs__needForGaps__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CG_Config_v1560_IEs__needForGaps__nat__Format CG_Config_v1560_IEs__needForGaps__F1 CG_Config_v1560_IEs__needForGaps__F2 CG_Config_v1560_IEs__needForGaps__F1F2 CG_Config_v1560_IEs__needForGaps__F2F1.

Opaque CG_Config_v1560_IEs__needForGaps__cond CG_Config_v1560_IEs__needForGaps__Format.


Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Format_Type := Eval cbn in seq_format_prod CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list.
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Format_list : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Format_Type :=
  (ARFCN_ValueEUTRA__Format, (EUTRA_PhysCellId__Format, unit_format)).
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list__Format := (*Eval compute in *) seq_format CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Format_list.
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1 z :=
  (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__eutraFrequency z, (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cellForWhichToReportCGI_EUTRA z, tt)).
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F2 (y : seq_type CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Type i0 i1
  end.
Lemma CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1F2_cond (z : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Type)
  : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond z ->
  (seq_cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1 z)).
intro H. unfold CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond in H. simpl. auto. Qed.
Lemma CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1F2_cond2 (z : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Type)
 : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F2 (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F2F1_cond (y : seq_type CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list)
  : seq_cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list y ->
 (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F2 y)) /\  CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1 (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond. simpl in *. auto.
 - simpl. unfold CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Format : T_Format CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Type CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond :=
        proj2_format  CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__list__Format
    CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1 CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F2 CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1F2_cond  CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F1F2_cond2 CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__F2F1_cond.
Opaque CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Format.


Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Format_Type := Eval cbn in seq_format_prod CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list.
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Format_list : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Format_Type :=
  (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA__Format, unit_format).
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list__Format := (*Eval compute in *) seq_format CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Format_list.
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1 z :=
  (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__requestedCellInfoEUTRA z, tt).
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F2 (y : seq_type CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list) :=
  match y with
  | (i0, _)=>
    make__CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Type i0
  end.
Lemma CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1F2_cond (z : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Type)
  : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond z ->
  (seq_cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1 z)).
intro H. unfold CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond in H. simpl. auto. Qed.
Lemma CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1F2_cond2 (z : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Type)
 : CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F2 (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F2F1_cond (y : seq_type CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list)
  : seq_cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list y ->
 (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F2 y)) /\  CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1 (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond. simpl in *. auto.
 - simpl. unfold CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Format : T_Format CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Type CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond :=
        proj2_format  CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__list__Format
    CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1 CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F2 CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1F2_cond  CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F1F2_cond2 CG_Config_v1560_IEs__reportCGI_RequestEUTRA__F2F1_cond.
Opaque CG_Config_v1560_IEs__reportCGI_RequestEUTRA__cond CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Format.


Definition CG_Config_v1560_IEs__Format_Type := Eval cbn in seq_format_prod CG_Config_v1560_IEs__list.
Definition CG_Config_v1560_IEs__Format_list : CG_Config_v1560_IEs__Format_Type :=
  (ARFCN_ValueEUTRA__Format, (octet_string_nc__Format, (octet_string_nc__Format, (CandidateServingFreqListEUTRA__Format, (CG_Config_v1560_IEs__needForGaps__Format, (DRX_Config__Format, (CG_Config_v1560_IEs__reportCGI_RequestEUTRA__Format, (CG_Config_v1590_IEs__Format, unit_format)))))))).
Definition CG_Config_v1560_IEs__list__Format := (*Eval compute in *) seq_format CG_Config_v1560_IEs__list CG_Config_v1560_IEs__Format_list.
Definition CG_Config_v1560_IEs__F1 z :=
  (CG_Config_v1560_IEs__pSCellFrequencyEUTRA z, (CG_Config_v1560_IEs__scg_CellGroupConfigEUTRA z, (CG_Config_v1560_IEs__candidateCellInfoListSN_EUTRA z, (CG_Config_v1560_IEs__candidateServingFreqListEUTRA z, (CG_Config_v1560_IEs__needForGaps z, (CG_Config_v1560_IEs__drx_ConfigSCG z, (CG_Config_v1560_IEs__reportCGI_RequestEUTRA z, (CG_Config_v1560_IEs__nonCriticalExtension z, tt)))))))).
Definition CG_Config_v1560_IEs__F2 (y : seq_type CG_Config_v1560_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__CG_Config_v1560_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma CG_Config_v1560_IEs__F1F2_cond (z : CG_Config_v1560_IEs__Type)
  : CG_Config_v1560_IEs__cond z ->
  (seq_cond CG_Config_v1560_IEs__list (CG_Config_v1560_IEs__F1 z)).
intro H. unfold CG_Config_v1560_IEs__cond in H. simpl. auto. Qed.
Lemma CG_Config_v1560_IEs__F1F2_cond2 (z : CG_Config_v1560_IEs__Type)
 : CG_Config_v1560_IEs__F2 (CG_Config_v1560_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CG_Config_v1560_IEs__F2F1_cond (y : seq_type CG_Config_v1560_IEs__list)
  : seq_cond CG_Config_v1560_IEs__list y ->
 (CG_Config_v1560_IEs__cond (CG_Config_v1560_IEs__F2 y)) /\  CG_Config_v1560_IEs__F1 (CG_Config_v1560_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CG_Config_v1560_IEs__cond. simpl in *. auto.
 - simpl. unfold CG_Config_v1560_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CG_Config_v1560_IEs__Format : T_Format CG_Config_v1560_IEs__Type CG_Config_v1560_IEs__cond :=
        proj2_format  CG_Config_v1560_IEs__cond CG_Config_v1560_IEs__list__Format
    CG_Config_v1560_IEs__F1 CG_Config_v1560_IEs__F2 CG_Config_v1560_IEs__F1F2_cond  CG_Config_v1560_IEs__F1F2_cond2 CG_Config_v1560_IEs__F2F1_cond.
Opaque CG_Config_v1560_IEs__cond CG_Config_v1560_IEs__Format.

