Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FailureReportSCG__failureType__Type : Set :=
 | FailureReportSCG__failureType__t310_Expiry
 | FailureReportSCG__failureType__randomAccessProblem
 | FailureReportSCG__failureType__rlc_MaxNumRetx
 | FailureReportSCG__failureType__synchReconfigFailureSCG
 | FailureReportSCG__failureType__scg_ReconfigFailure
 | FailureReportSCG__failureType__srb3_IntegrityFailure
 | FailureReportSCG__failureType__other_r16
 | FailureReportSCG__failureType__spare1
.
Definition FailureReportSCG__failureType__cond := (fun (_ : FailureReportSCG__failureType__Type) => True).
Lemma FailureReportSCG__failureType__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FailureReportSCG__failureType__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 FailureReportSCG__failureType__nat__helper.

Definition FailureReportSCG__failureType__F1 t :=
  match t with
  | FailureReportSCG__failureType__t310_Expiry => 0
  | FailureReportSCG__failureType__randomAccessProblem => 1
  | FailureReportSCG__failureType__rlc_MaxNumRetx => 2
  | FailureReportSCG__failureType__synchReconfigFailureSCG => 3
  | FailureReportSCG__failureType__scg_ReconfigFailure => 4
  | FailureReportSCG__failureType__srb3_IntegrityFailure => 5
  | FailureReportSCG__failureType__other_r16 => 6
  | FailureReportSCG__failureType__spare1 => 7
  end.
Definition FailureReportSCG__failureType__F2 n :=
  match n with
  | 0 => FailureReportSCG__failureType__t310_Expiry
  | 1 => FailureReportSCG__failureType__randomAccessProblem
  | 2 => FailureReportSCG__failureType__rlc_MaxNumRetx
  | 3 => FailureReportSCG__failureType__synchReconfigFailureSCG
  | 4 => FailureReportSCG__failureType__scg_ReconfigFailure
  | 5 => FailureReportSCG__failureType__srb3_IntegrityFailure
  | 6 => FailureReportSCG__failureType__other_r16
  | 7 => FailureReportSCG__failureType__spare1
  | _ => FailureReportSCG__failureType__t310_Expiry
  end.
Lemma FailureReportSCG__failureType__F1F2 : forall x : FailureReportSCG__failureType__Type, (FailureReportSCG__failureType__F1 x <= 7) /\ FailureReportSCG__failureType__F2 (FailureReportSCG__failureType__F1 x) = x. imp_solve. Qed.
Lemma FailureReportSCG__failureType__F2F1 : forall (y : nat) (H : y <= 7), FailureReportSCG__failureType__F1 (FailureReportSCG__failureType__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasResultFreqList.

Opaque MeasResultFreqList__cond MeasResultFreqList__Format.

Require Import NR.LocationInfo_r16.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

Inductive FailureReportSCG__ext0O__failureType_v1610__Type : Set :=
 | FailureReportSCG__ext0O__failureType_v1610__scg_lbtFailure_r16
 | FailureReportSCG__ext0O__failureType_v1610__beamFailureRecoveryFailure_r16
 | FailureReportSCG__ext0O__failureType_v1610__t312_Expiry_r16
 | FailureReportSCG__ext0O__failureType_v1610__bh_RLF_r16
 | FailureReportSCG__ext0O__failureType_v1610__beamFailure_r17
 | FailureReportSCG__ext0O__failureType_v1610__spare3
 | FailureReportSCG__ext0O__failureType_v1610__spare2
 | FailureReportSCG__ext0O__failureType_v1610__spare1
.
Definition FailureReportSCG__ext0O__failureType_v1610__cond := (fun (_ : FailureReportSCG__ext0O__failureType_v1610__Type) => True).
Lemma FailureReportSCG__ext0O__failureType_v1610__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FailureReportSCG__ext0O__failureType_v1610__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 FailureReportSCG__ext0O__failureType_v1610__nat__helper.

Definition FailureReportSCG__ext0O__failureType_v1610__F1 t :=
  match t with
  | FailureReportSCG__ext0O__failureType_v1610__scg_lbtFailure_r16 => 0
  | FailureReportSCG__ext0O__failureType_v1610__beamFailureRecoveryFailure_r16 => 1
  | FailureReportSCG__ext0O__failureType_v1610__t312_Expiry_r16 => 2
  | FailureReportSCG__ext0O__failureType_v1610__bh_RLF_r16 => 3
  | FailureReportSCG__ext0O__failureType_v1610__beamFailure_r17 => 4
  | FailureReportSCG__ext0O__failureType_v1610__spare3 => 5
  | FailureReportSCG__ext0O__failureType_v1610__spare2 => 6
  | FailureReportSCG__ext0O__failureType_v1610__spare1 => 7
  end.
Definition FailureReportSCG__ext0O__failureType_v1610__F2 n :=
  match n with
  | 0 => FailureReportSCG__ext0O__failureType_v1610__scg_lbtFailure_r16
  | 1 => FailureReportSCG__ext0O__failureType_v1610__beamFailureRecoveryFailure_r16
  | 2 => FailureReportSCG__ext0O__failureType_v1610__t312_Expiry_r16
  | 3 => FailureReportSCG__ext0O__failureType_v1610__bh_RLF_r16
  | 4 => FailureReportSCG__ext0O__failureType_v1610__beamFailure_r17
  | 5 => FailureReportSCG__ext0O__failureType_v1610__spare3
  | 6 => FailureReportSCG__ext0O__failureType_v1610__spare2
  | 7 => FailureReportSCG__ext0O__failureType_v1610__spare1
  | _ => FailureReportSCG__ext0O__failureType_v1610__scg_lbtFailure_r16
  end.
Lemma FailureReportSCG__ext0O__failureType_v1610__F1F2 : forall x : FailureReportSCG__ext0O__failureType_v1610__Type, (FailureReportSCG__ext0O__failureType_v1610__F1 x <= 7) /\ FailureReportSCG__ext0O__failureType_v1610__F2 (FailureReportSCG__ext0O__failureType_v1610__F1 x) = x. imp_solve. Qed.
Lemma FailureReportSCG__ext0O__failureType_v1610__F2F1 : forall (y : nat) (H : y <= 7), FailureReportSCG__ext0O__failureType_v1610__F1 (FailureReportSCG__ext0O__failureType_v1610__F2 y) = y. enum_solve H y. Qed.

Record FailureReportSCG__ext0O__Type : Set :=
  make__FailureReportSCG__ext0O__Type {
    FailureReportSCG__ext0O__locationInfo_r16 : option LocationInfo_r16__Type ;
    FailureReportSCG__ext0O__failureType_v1610 : option FailureReportSCG__ext0O__failureType_v1610__Type ;
}.
Definition FailureReportSCG__ext0O__list := (
 Opt LocationInfo_r16__Type LocationInfo_r16__cond ::
 Opt FailureReportSCG__ext0O__failureType_v1610__Type FailureReportSCG__ext0O__failureType_v1610__cond ::
 nil).
Definition FailureReportSCG__ext0O__cond z := 
  opt_cond LocationInfo_r16__cond (FailureReportSCG__ext0O__locationInfo_r16 z) /\
  opt_cond FailureReportSCG__ext0O__failureType_v1610__cond (FailureReportSCG__ext0O__failureType_v1610 z) /\
  True.

Definition FailureReportSCG__ext0__Type := FailureReportSCG__ext0O__Type.
Definition FailureReportSCG__ext0__cond := FailureReportSCG__ext0O__cond.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Record FailureReportSCG__ext1O__previousPSCellId_r17__Type : Set :=
  make__FailureReportSCG__ext1O__previousPSCellId_r17__Type {
    FailureReportSCG__ext1O__previousPSCellId_r17__physCellId_r17 : PhysCellId__Type ;
    FailureReportSCG__ext1O__previousPSCellId_r17__carrierFreq_r17 : ARFCN_ValueNR__Type ;
}.
Definition FailureReportSCG__ext1O__previousPSCellId_r17__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 nil).
Definition FailureReportSCG__ext1O__previousPSCellId_r17__cond z := 
  PhysCellId__cond (FailureReportSCG__ext1O__previousPSCellId_r17__physCellId_r17 z) /\
  ARFCN_ValueNR__cond (FailureReportSCG__ext1O__previousPSCellId_r17__carrierFreq_r17 z) /\
  True.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Record FailureReportSCG__ext1O__failedPSCellId_r17__Type : Set :=
  make__FailureReportSCG__ext1O__failedPSCellId_r17__Type {
    FailureReportSCG__ext1O__failedPSCellId_r17__physCellId_r17 : PhysCellId__Type ;
    FailureReportSCG__ext1O__failedPSCellId_r17__carrierFreq_r17 : ARFCN_ValueNR__Type ;
}.
Definition FailureReportSCG__ext1O__failedPSCellId_r17__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 nil).
Definition FailureReportSCG__ext1O__failedPSCellId_r17__cond z := 
  PhysCellId__cond (FailureReportSCG__ext1O__failedPSCellId_r17__physCellId_r17 z) /\
  ARFCN_ValueNR__cond (FailureReportSCG__ext1O__failedPSCellId_r17__carrierFreq_r17 z) /\
  True.

Lemma FailureReportSCG__ext1O__timeSCGFailure_r17__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma FailureReportSCG__ext1O__timeSCGFailure_r17__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply FailureReportSCG__ext1O__timeSCGFailure_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FailureReportSCG__ext1O__timeSCGFailure_r17__Type := Z.
Definition FailureReportSCG__ext1O__timeSCGFailure_r17__cond := (fun z => (0 <= z <= 1023)%Z).
Require Import NR.PerRAInfoList_r16.

Opaque PerRAInfoList_r16__cond PerRAInfoList_r16__Format.

Record FailureReportSCG__ext1O__Type : Set :=
  make__FailureReportSCG__ext1O__Type {
    FailureReportSCG__ext1O__previousPSCellId_r17 : option FailureReportSCG__ext1O__previousPSCellId_r17__Type ;
    FailureReportSCG__ext1O__failedPSCellId_r17 : option FailureReportSCG__ext1O__failedPSCellId_r17__Type ;
    FailureReportSCG__ext1O__timeSCGFailure_r17 : option Z ;
    FailureReportSCG__ext1O__perRAInfoList_r17 : option PerRAInfoList_r16__Type ;
}.
Definition FailureReportSCG__ext1O__list := (
 Opt FailureReportSCG__ext1O__previousPSCellId_r17__Type FailureReportSCG__ext1O__previousPSCellId_r17__cond ::
 Opt FailureReportSCG__ext1O__failedPSCellId_r17__Type FailureReportSCG__ext1O__failedPSCellId_r17__cond ::
 Opt Z FailureReportSCG__ext1O__timeSCGFailure_r17__cond ::
 Opt PerRAInfoList_r16__Type PerRAInfoList_r16__cond ::
 nil).
Definition FailureReportSCG__ext1O__cond z := 
  opt_cond FailureReportSCG__ext1O__previousPSCellId_r17__cond (FailureReportSCG__ext1O__previousPSCellId_r17 z) /\
  opt_cond FailureReportSCG__ext1O__failedPSCellId_r17__cond (FailureReportSCG__ext1O__failedPSCellId_r17 z) /\
  opt_cond FailureReportSCG__ext1O__timeSCGFailure_r17__cond (FailureReportSCG__ext1O__timeSCGFailure_r17 z) /\
  opt_cond PerRAInfoList_r16__cond (FailureReportSCG__ext1O__perRAInfoList_r17 z) /\
  True.

Definition FailureReportSCG__ext1__Type := FailureReportSCG__ext1O__Type.
Definition FailureReportSCG__ext1__cond := FailureReportSCG__ext1O__cond.

Record FailureReportSCG__Type : Set :=
  make__FailureReportSCG__Type {
    FailureReportSCG__failureType : FailureReportSCG__failureType__Type ;
    FailureReportSCG__measResultFreqList : option MeasResultFreqList__Type ;
    FailureReportSCG__measResultSCG_Failure : option octet_string ;
    FailureReportSCG__ext0 : option FailureReportSCG__ext0__Type ;
    FailureReportSCG__ext1 : option FailureReportSCG__ext1__Type ;
}.
Definition FailureReportSCG__root_list : list seq_elem := (
 Nor FailureReportSCG__failureType__Type FailureReportSCG__failureType__cond ::
 Opt MeasResultFreqList__Type MeasResultFreqList__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition FailureReportSCG__ext_list : list typ := (
  typ_cons FailureReportSCG__ext0__Type FailureReportSCG__ext0__cond ::
  typ_cons FailureReportSCG__ext1__Type FailureReportSCG__ext1__cond ::
  nil).
Definition FailureReportSCG__cond (z : FailureReportSCG__Type) := 
(  FailureReportSCG__failureType__cond (FailureReportSCG__failureType z) /\
  opt_cond MeasResultFreqList__cond (FailureReportSCG__measResultFreqList z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (FailureReportSCG__measResultSCG_Failure z) /\
  True) /\ 
(  opt_cond FailureReportSCG__ext0__cond (FailureReportSCG__ext0 z) /\
  opt_cond FailureReportSCG__ext1__cond (FailureReportSCG__ext1 z) /\
  True).


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
Definition FailureReportSCG__failureType__Format : T_Format FailureReportSCG__failureType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FailureReportSCG__failureType__nat__Format FailureReportSCG__failureType__F1 FailureReportSCG__failureType__F2 FailureReportSCG__failureType__F1F2 FailureReportSCG__failureType__F2F1.

Opaque FailureReportSCG__failureType__cond FailureReportSCG__failureType__Format.

Definition FailureReportSCG__ext0O__failureType_v1610__Format : T_Format FailureReportSCG__ext0O__failureType_v1610__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FailureReportSCG__ext0O__failureType_v1610__nat__Format FailureReportSCG__ext0O__failureType_v1610__F1 FailureReportSCG__ext0O__failureType_v1610__F2 FailureReportSCG__ext0O__failureType_v1610__F1F2 FailureReportSCG__ext0O__failureType_v1610__F2F1.

Opaque FailureReportSCG__ext0O__failureType_v1610__cond FailureReportSCG__ext0O__failureType_v1610__Format.


Definition FailureReportSCG__ext0O__Format_Type := Eval cbn in seq_format_prod FailureReportSCG__ext0O__list.
Definition FailureReportSCG__ext0O__Format_list : FailureReportSCG__ext0O__Format_Type :=
  (LocationInfo_r16__Format, (FailureReportSCG__ext0O__failureType_v1610__Format, unit_format)).
Definition FailureReportSCG__ext0O__list__Format := (*Eval compute in *) seq_format FailureReportSCG__ext0O__list FailureReportSCG__ext0O__Format_list.
Definition FailureReportSCG__ext0O__F1 z :=
  (FailureReportSCG__ext0O__locationInfo_r16 z, (FailureReportSCG__ext0O__failureType_v1610 z, tt)).
Definition FailureReportSCG__ext0O__F2 (y : seq_type FailureReportSCG__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FailureReportSCG__ext0O__Type i0 i1
  end.
Lemma FailureReportSCG__ext0O__F1F2_cond (z : FailureReportSCG__ext0O__Type)
  : FailureReportSCG__ext0O__cond z ->
  (seq_cond FailureReportSCG__ext0O__list (FailureReportSCG__ext0O__F1 z)).
intro H. unfold FailureReportSCG__ext0O__cond in H. simpl. auto. Qed.
Lemma FailureReportSCG__ext0O__F1F2_cond2 (z : FailureReportSCG__ext0O__Type)
 : FailureReportSCG__ext0O__F2 (FailureReportSCG__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FailureReportSCG__ext0O__F2F1_cond (y : seq_type FailureReportSCG__ext0O__list)
  : seq_cond FailureReportSCG__ext0O__list y ->
 (FailureReportSCG__ext0O__cond (FailureReportSCG__ext0O__F2 y)) /\  FailureReportSCG__ext0O__F1 (FailureReportSCG__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FailureReportSCG__ext0O__cond. simpl in *. auto.
 - simpl. unfold FailureReportSCG__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FailureReportSCG__ext0O__Format : T_Format FailureReportSCG__ext0O__Type FailureReportSCG__ext0O__cond :=
        proj2_format  FailureReportSCG__ext0O__cond FailureReportSCG__ext0O__list__Format
    FailureReportSCG__ext0O__F1 FailureReportSCG__ext0O__F2 FailureReportSCG__ext0O__F1F2_cond  FailureReportSCG__ext0O__F1F2_cond2 FailureReportSCG__ext0O__F2F1_cond.
Opaque FailureReportSCG__ext0O__cond FailureReportSCG__ext0O__Format.

Definition FailureReportSCG__ext0__check_all_none (b : FailureReportSCG__ext0O__Type) : bool :=
match b with 
  | make__FailureReportSCG__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition FailureReportSCG__ext0__Format : T_Format FailureReportSCG__ext0__Type FailureReportSCG__ext0__cond :=
  restrict_add_format FailureReportSCG__ext0__check_all_none FailureReportSCG__ext0O__Format.

Opaque FailureReportSCG__ext0__cond FailureReportSCG__ext0__Format.


Definition FailureReportSCG__ext1O__previousPSCellId_r17__Format_Type := Eval cbn in seq_format_prod FailureReportSCG__ext1O__previousPSCellId_r17__list.
Definition FailureReportSCG__ext1O__previousPSCellId_r17__Format_list : FailureReportSCG__ext1O__previousPSCellId_r17__Format_Type :=
  (PhysCellId__Format, (ARFCN_ValueNR__Format, unit_format)).
Definition FailureReportSCG__ext1O__previousPSCellId_r17__list__Format := (*Eval compute in *) seq_format FailureReportSCG__ext1O__previousPSCellId_r17__list FailureReportSCG__ext1O__previousPSCellId_r17__Format_list.
Definition FailureReportSCG__ext1O__previousPSCellId_r17__F1 z :=
  (FailureReportSCG__ext1O__previousPSCellId_r17__physCellId_r17 z, (FailureReportSCG__ext1O__previousPSCellId_r17__carrierFreq_r17 z, tt)).
Definition FailureReportSCG__ext1O__previousPSCellId_r17__F2 (y : seq_type FailureReportSCG__ext1O__previousPSCellId_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FailureReportSCG__ext1O__previousPSCellId_r17__Type i0 i1
  end.
Lemma FailureReportSCG__ext1O__previousPSCellId_r17__F1F2_cond (z : FailureReportSCG__ext1O__previousPSCellId_r17__Type)
  : FailureReportSCG__ext1O__previousPSCellId_r17__cond z ->
  (seq_cond FailureReportSCG__ext1O__previousPSCellId_r17__list (FailureReportSCG__ext1O__previousPSCellId_r17__F1 z)).
intro H. unfold FailureReportSCG__ext1O__previousPSCellId_r17__cond in H. simpl. auto. Qed.
Lemma FailureReportSCG__ext1O__previousPSCellId_r17__F1F2_cond2 (z : FailureReportSCG__ext1O__previousPSCellId_r17__Type)
 : FailureReportSCG__ext1O__previousPSCellId_r17__F2 (FailureReportSCG__ext1O__previousPSCellId_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FailureReportSCG__ext1O__previousPSCellId_r17__F2F1_cond (y : seq_type FailureReportSCG__ext1O__previousPSCellId_r17__list)
  : seq_cond FailureReportSCG__ext1O__previousPSCellId_r17__list y ->
 (FailureReportSCG__ext1O__previousPSCellId_r17__cond (FailureReportSCG__ext1O__previousPSCellId_r17__F2 y)) /\  FailureReportSCG__ext1O__previousPSCellId_r17__F1 (FailureReportSCG__ext1O__previousPSCellId_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FailureReportSCG__ext1O__previousPSCellId_r17__cond. simpl in *. auto.
 - simpl. unfold FailureReportSCG__ext1O__previousPSCellId_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FailureReportSCG__ext1O__previousPSCellId_r17__Format : T_Format FailureReportSCG__ext1O__previousPSCellId_r17__Type FailureReportSCG__ext1O__previousPSCellId_r17__cond :=
        proj2_format  FailureReportSCG__ext1O__previousPSCellId_r17__cond FailureReportSCG__ext1O__previousPSCellId_r17__list__Format
    FailureReportSCG__ext1O__previousPSCellId_r17__F1 FailureReportSCG__ext1O__previousPSCellId_r17__F2 FailureReportSCG__ext1O__previousPSCellId_r17__F1F2_cond  FailureReportSCG__ext1O__previousPSCellId_r17__F1F2_cond2 FailureReportSCG__ext1O__previousPSCellId_r17__F2F1_cond.
Opaque FailureReportSCG__ext1O__previousPSCellId_r17__cond FailureReportSCG__ext1O__previousPSCellId_r17__Format.


Definition FailureReportSCG__ext1O__failedPSCellId_r17__Format_Type := Eval cbn in seq_format_prod FailureReportSCG__ext1O__failedPSCellId_r17__list.
Definition FailureReportSCG__ext1O__failedPSCellId_r17__Format_list : FailureReportSCG__ext1O__failedPSCellId_r17__Format_Type :=
  (PhysCellId__Format, (ARFCN_ValueNR__Format, unit_format)).
Definition FailureReportSCG__ext1O__failedPSCellId_r17__list__Format := (*Eval compute in *) seq_format FailureReportSCG__ext1O__failedPSCellId_r17__list FailureReportSCG__ext1O__failedPSCellId_r17__Format_list.
Definition FailureReportSCG__ext1O__failedPSCellId_r17__F1 z :=
  (FailureReportSCG__ext1O__failedPSCellId_r17__physCellId_r17 z, (FailureReportSCG__ext1O__failedPSCellId_r17__carrierFreq_r17 z, tt)).
Definition FailureReportSCG__ext1O__failedPSCellId_r17__F2 (y : seq_type FailureReportSCG__ext1O__failedPSCellId_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FailureReportSCG__ext1O__failedPSCellId_r17__Type i0 i1
  end.
Lemma FailureReportSCG__ext1O__failedPSCellId_r17__F1F2_cond (z : FailureReportSCG__ext1O__failedPSCellId_r17__Type)
  : FailureReportSCG__ext1O__failedPSCellId_r17__cond z ->
  (seq_cond FailureReportSCG__ext1O__failedPSCellId_r17__list (FailureReportSCG__ext1O__failedPSCellId_r17__F1 z)).
intro H. unfold FailureReportSCG__ext1O__failedPSCellId_r17__cond in H. simpl. auto. Qed.
Lemma FailureReportSCG__ext1O__failedPSCellId_r17__F1F2_cond2 (z : FailureReportSCG__ext1O__failedPSCellId_r17__Type)
 : FailureReportSCG__ext1O__failedPSCellId_r17__F2 (FailureReportSCG__ext1O__failedPSCellId_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FailureReportSCG__ext1O__failedPSCellId_r17__F2F1_cond (y : seq_type FailureReportSCG__ext1O__failedPSCellId_r17__list)
  : seq_cond FailureReportSCG__ext1O__failedPSCellId_r17__list y ->
 (FailureReportSCG__ext1O__failedPSCellId_r17__cond (FailureReportSCG__ext1O__failedPSCellId_r17__F2 y)) /\  FailureReportSCG__ext1O__failedPSCellId_r17__F1 (FailureReportSCG__ext1O__failedPSCellId_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FailureReportSCG__ext1O__failedPSCellId_r17__cond. simpl in *. auto.
 - simpl. unfold FailureReportSCG__ext1O__failedPSCellId_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FailureReportSCG__ext1O__failedPSCellId_r17__Format : T_Format FailureReportSCG__ext1O__failedPSCellId_r17__Type FailureReportSCG__ext1O__failedPSCellId_r17__cond :=
        proj2_format  FailureReportSCG__ext1O__failedPSCellId_r17__cond FailureReportSCG__ext1O__failedPSCellId_r17__list__Format
    FailureReportSCG__ext1O__failedPSCellId_r17__F1 FailureReportSCG__ext1O__failedPSCellId_r17__F2 FailureReportSCG__ext1O__failedPSCellId_r17__F1F2_cond  FailureReportSCG__ext1O__failedPSCellId_r17__F1F2_cond2 FailureReportSCG__ext1O__failedPSCellId_r17__F2F1_cond.
Opaque FailureReportSCG__ext1O__failedPSCellId_r17__cond FailureReportSCG__ext1O__failedPSCellId_r17__Format.

Definition FailureReportSCG__ext1O__timeSCGFailure_r17__Format : T_Format Z FailureReportSCG__ext1O__timeSCGFailure_r17__cond :=
 ranged_int_format (0) (1023) FailureReportSCG__ext1O__timeSCGFailure_r17__helper1 FailureReportSCG__ext1O__timeSCGFailure_r17__helper2.

Opaque FailureReportSCG__ext1O__timeSCGFailure_r17__cond FailureReportSCG__ext1O__timeSCGFailure_r17__Format.


Definition FailureReportSCG__ext1O__Format_Type := Eval cbn in seq_format_prod FailureReportSCG__ext1O__list.
Definition FailureReportSCG__ext1O__Format_list : FailureReportSCG__ext1O__Format_Type :=
  (FailureReportSCG__ext1O__previousPSCellId_r17__Format, (FailureReportSCG__ext1O__failedPSCellId_r17__Format, (FailureReportSCG__ext1O__timeSCGFailure_r17__Format, (PerRAInfoList_r16__Format, unit_format)))).
Definition FailureReportSCG__ext1O__list__Format := (*Eval compute in *) seq_format FailureReportSCG__ext1O__list FailureReportSCG__ext1O__Format_list.
Definition FailureReportSCG__ext1O__F1 z :=
  (FailureReportSCG__ext1O__previousPSCellId_r17 z, (FailureReportSCG__ext1O__failedPSCellId_r17 z, (FailureReportSCG__ext1O__timeSCGFailure_r17 z, (FailureReportSCG__ext1O__perRAInfoList_r17 z, tt)))).
Definition FailureReportSCG__ext1O__F2 (y : seq_type FailureReportSCG__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__FailureReportSCG__ext1O__Type i0 i1 i2 i3
  end.
Lemma FailureReportSCG__ext1O__F1F2_cond (z : FailureReportSCG__ext1O__Type)
  : FailureReportSCG__ext1O__cond z ->
  (seq_cond FailureReportSCG__ext1O__list (FailureReportSCG__ext1O__F1 z)).
intro H. unfold FailureReportSCG__ext1O__cond in H. simpl. auto. Qed.
Lemma FailureReportSCG__ext1O__F1F2_cond2 (z : FailureReportSCG__ext1O__Type)
 : FailureReportSCG__ext1O__F2 (FailureReportSCG__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FailureReportSCG__ext1O__F2F1_cond (y : seq_type FailureReportSCG__ext1O__list)
  : seq_cond FailureReportSCG__ext1O__list y ->
 (FailureReportSCG__ext1O__cond (FailureReportSCG__ext1O__F2 y)) /\  FailureReportSCG__ext1O__F1 (FailureReportSCG__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FailureReportSCG__ext1O__cond. simpl in *. auto.
 - simpl. unfold FailureReportSCG__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FailureReportSCG__ext1O__Format : T_Format FailureReportSCG__ext1O__Type FailureReportSCG__ext1O__cond :=
        proj2_format  FailureReportSCG__ext1O__cond FailureReportSCG__ext1O__list__Format
    FailureReportSCG__ext1O__F1 FailureReportSCG__ext1O__F2 FailureReportSCG__ext1O__F1F2_cond  FailureReportSCG__ext1O__F1F2_cond2 FailureReportSCG__ext1O__F2F1_cond.
Opaque FailureReportSCG__ext1O__cond FailureReportSCG__ext1O__Format.

Definition FailureReportSCG__ext1__check_all_none (b : FailureReportSCG__ext1O__Type) : bool :=
match b with 
  | make__FailureReportSCG__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition FailureReportSCG__ext1__Format : T_Format FailureReportSCG__ext1__Type FailureReportSCG__ext1__cond :=
  restrict_add_format FailureReportSCG__ext1__check_all_none FailureReportSCG__ext1O__Format.

Opaque FailureReportSCG__ext1__cond FailureReportSCG__ext1__Format.


Definition FailureReportSCG__root_Format_Type := Eval cbn in seq_format_prod FailureReportSCG__root_list.
Definition FailureReportSCG__root_Format_list : FailureReportSCG__root_Format_Type :=
  (FailureReportSCG__failureType__Format, (MeasResultFreqList__Format, (octet_string_nc__Format, unit_format))).

Definition FailureReportSCG__ext_Format_Type := Eval cbn in get_formats FailureReportSCG__ext_list.
Definition FailureReportSCG__ext_Format_list : FailureReportSCG__ext_Format_Type :=
  (FailureReportSCG__ext0__Format, (FailureReportSCG__ext1__Format, unit__Format)).

Definition FailureReportSCG__list_type : Set := (seq_type FailureReportSCG__root_list) * (seq_ext_type FailureReportSCG__ext_list).
Definition FailureReportSCG__list_cond (z : FailureReportSCG__list_type) : Prop :=
        (seq_cond FailureReportSCG__root_list (fst z)) /\ (seq_ext_cond FailureReportSCG__ext_list (snd z)).
Definition FailureReportSCG__list_format : T_Format FailureReportSCG__list_type FailureReportSCG__list_cond :=
 (* Eval compute in *) seq_ext_format FailureReportSCG__root_list FailureReportSCG__root_Format_list FailureReportSCG__ext_list FailureReportSCG__ext_Format_list.

Opaque FailureReportSCG__list_format.
Definition FailureReportSCG__F1 (z : FailureReportSCG__Type) : FailureReportSCG__list_type :=
  (((FailureReportSCG__failureType z, (FailureReportSCG__measResultFreqList z, (FailureReportSCG__measResultSCG_Failure z, tt)))), (
(FailureReportSCG__ext0 z, (FailureReportSCG__ext1 z, tt)))).
Definition FailureReportSCG__F2 (y : FailureReportSCG__list_type) : FailureReportSCG__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, _)))=>
    make__FailureReportSCG__Type j0 j1 j2 i0 i1
  end.
Definition FailureReportSCG__helper1 : (forall a : FailureReportSCG__Type, FailureReportSCG__cond a -> FailureReportSCG__list_cond (FailureReportSCG__F1 a)).
                     intros. destruct a. auto. Qed.
Definition FailureReportSCG__helper2 : (forall a : FailureReportSCG__Type, FailureReportSCG__F2 (FailureReportSCG__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition FailureReportSCG__helper3 : (forall b : FailureReportSCG__list_type, FailureReportSCG__list_cond b -> FailureReportSCG__cond (FailureReportSCG__F2 b) /\ FailureReportSCG__F1 (FailureReportSCG__F2 b) = b).
                     intros. destruct b as [y y1]. unfold FailureReportSCG__cond, FailureReportSCG__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition FailureReportSCG__Format : T_Format FailureReportSCG__Type FailureReportSCG__cond :=
 proj2_format FailureReportSCG__cond FailureReportSCG__list_format  FailureReportSCG__F1 FailureReportSCG__F2 FailureReportSCG__helper1 FailureReportSCG__helper2 FailureReportSCG__helper3.

Opaque FailureReportSCG__cond FailureReportSCG__Format.

