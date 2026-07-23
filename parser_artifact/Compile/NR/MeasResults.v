Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasId.

Opaque MeasId__cond MeasId__Format.

Require Import NR.MeasResultServMOList.

Opaque MeasResultServMOList__cond MeasResultServMOList__Format.

Require Import NR.MeasResultListNR.

Opaque MeasResultListNR__cond MeasResultListNR__Format.


Inductive MeasResults__measResultNeighCells__root__Type : Set := | MeasResults__measResultNeighCells__root__measResultListNR : MeasResultListNR__Type -> MeasResults__measResultNeighCells__root__Type.
Definition MeasResults__measResultNeighCells__root__cond (c : MeasResults__measResultNeighCells__root__Type) := 
  match c with
  | MeasResults__measResultNeighCells__root__measResultListNR t => MeasResultListNR__cond t 
  end.

Require Import NR.MeasResultListEUTRA.

Opaque MeasResultListEUTRA__cond MeasResultListEUTRA__Format.

Require Import NR.MeasResultListUTRA_FDD_r16.

Opaque MeasResultListUTRA_FDD_r16__cond MeasResultListUTRA_FDD_r16__Format.


Inductive MeasResults__measResultNeighCells__ext__Type : Set :=
  | MeasResults__measResultNeighCells__ext__measResultListEUTRA : MeasResultListEUTRA__Type -> MeasResults__measResultNeighCells__ext__Type
  | MeasResults__measResultNeighCells__ext__measResultListUTRA_FDD_r16 : MeasResultListUTRA_FDD_r16__Type -> MeasResults__measResultNeighCells__ext__Type
  | MeasResults__measResultNeighCells__ext__sl_MeasResultsCandRelay_r17 : octet_string -> MeasResults__measResultNeighCells__ext__Type
.
Definition MeasResults__measResultNeighCells__ext__list : list typ := (
typ_cons MeasResultListEUTRA__Type MeasResultListEUTRA__cond ::
typ_cons MeasResultListUTRA_FDD_r16__Type MeasResultListUTRA_FDD_r16__cond ::
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition MeasResults__measResultNeighCells__ext__cond (c : MeasResults__measResultNeighCells__ext__Type) := 
  match c with
  | MeasResults__measResultNeighCells__ext__measResultListEUTRA t => MeasResultListEUTRA__cond t 
  | MeasResults__measResultNeighCells__ext__measResultListUTRA_FDD_r16 t => MeasResultListUTRA_FDD_r16__cond t 
  | MeasResults__measResultNeighCells__ext__sl_MeasResultsCandRelay_r17 t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  end.

Lemma MeasResults__measResultNeighCells__ext__len_helper1 : to_bit_sz (length MeasResults__measResultNeighCells__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition MeasResults__measResultNeighCells__Type : Set := MeasResults__measResultNeighCells__root__Type + MeasResults__measResultNeighCells__ext__Type.
Definition MeasResults__measResultNeighCells__cond :=
  sum_cond MeasResults__measResultNeighCells__root__cond MeasResults__measResultNeighCells__ext__cond.
Require Import NR.MeasResultServFreqListEUTRA_SCG.

Opaque MeasResultServFreqListEUTRA_SCG__cond MeasResultServFreqListEUTRA_SCG__Format.

Require Import NR.MeasResultServFreqListNR_SCG.

Opaque MeasResultServFreqListNR_SCG__cond MeasResultServFreqListNR_SCG__Format.

Require Import NR.MeasResultSFTD_EUTRA.

Opaque MeasResultSFTD_EUTRA__cond MeasResultSFTD_EUTRA__Format.

Require Import NR.MeasResultCellSFTD_NR.

Opaque MeasResultCellSFTD_NR__cond MeasResultCellSFTD_NR__Format.

Record MeasResults__ext0O__Type : Set :=
  make__MeasResults__ext0O__Type {
    MeasResults__ext0O__measResultServFreqListEUTRA_SCG : option MeasResultServFreqListEUTRA_SCG__Type ;
    MeasResults__ext0O__measResultServFreqListNR_SCG : option MeasResultServFreqListNR_SCG__Type ;
    MeasResults__ext0O__measResultSFTD_EUTRA : option MeasResultSFTD_EUTRA__Type ;
    MeasResults__ext0O__measResultSFTD_NR : option MeasResultCellSFTD_NR__Type ;
}.
Definition MeasResults__ext0O__list := (
 Opt MeasResultServFreqListEUTRA_SCG__Type MeasResultServFreqListEUTRA_SCG__cond ::
 Opt MeasResultServFreqListNR_SCG__Type MeasResultServFreqListNR_SCG__cond ::
 Opt MeasResultSFTD_EUTRA__Type MeasResultSFTD_EUTRA__cond ::
 Opt MeasResultCellSFTD_NR__Type MeasResultCellSFTD_NR__cond ::
 nil).
Definition MeasResults__ext0O__cond z := 
  opt_cond MeasResultServFreqListEUTRA_SCG__cond (MeasResults__ext0O__measResultServFreqListEUTRA_SCG z) /\
  opt_cond MeasResultServFreqListNR_SCG__cond (MeasResults__ext0O__measResultServFreqListNR_SCG z) /\
  opt_cond MeasResultSFTD_EUTRA__cond (MeasResults__ext0O__measResultSFTD_EUTRA z) /\
  opt_cond MeasResultCellSFTD_NR__cond (MeasResults__ext0O__measResultSFTD_NR z) /\
  True.

Definition MeasResults__ext0__Type := MeasResults__ext0O__Type.
Definition MeasResults__ext0__cond := MeasResults__ext0O__cond.

Require Import NR.MeasResultCellListSFTD_NR.

Opaque MeasResultCellListSFTD_NR__cond MeasResultCellListSFTD_NR__Format.

Record MeasResults__ext1O__Type : Set :=
  make__MeasResults__ext1O__Type {
    MeasResults__ext1O__measResultCellListSFTD_NR : option MeasResultCellListSFTD_NR__Type ;
}.
Definition MeasResults__ext1O__list := (
 Opt MeasResultCellListSFTD_NR__Type MeasResultCellListSFTD_NR__cond ::
 nil).
Definition MeasResults__ext1O__cond z := 
  opt_cond MeasResultCellListSFTD_NR__cond (MeasResults__ext1O__measResultCellListSFTD_NR z) /\
  True.

Definition MeasResults__ext1__Type := MeasResults__ext1O__Type.
Definition MeasResults__ext1__cond := MeasResults__ext1O__cond.

Require Import NR.MeasResultForRSSI_r16.

Opaque MeasResultForRSSI_r16__cond MeasResultForRSSI_r16__Format.

Require Import NR.LocationInfo_r16.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

Require Import NR.UL_PDCP_DelayValueResultList_r16.

Opaque UL_PDCP_DelayValueResultList_r16__cond UL_PDCP_DelayValueResultList_r16__Format.

Require Import NR.MeasResultsSL_r16.

Opaque MeasResultsSL_r16__cond MeasResultsSL_r16__Format.

Require Import NR.MeasResultCLI_r16.

Opaque MeasResultCLI_r16__cond MeasResultCLI_r16__Format.

Record MeasResults__ext2O__Type : Set :=
  make__MeasResults__ext2O__Type {
    MeasResults__ext2O__measResultForRSSI_r16 : option MeasResultForRSSI_r16__Type ;
    MeasResults__ext2O__locationInfo_r16 : option LocationInfo_r16__Type ;
    MeasResults__ext2O__ul_PDCP_DelayValueResultList_r16 : option UL_PDCP_DelayValueResultList_r16__Type ;
    MeasResults__ext2O__measResultsSL_r16 : option MeasResultsSL_r16__Type ;
    MeasResults__ext2O__measResultCLI_r16 : option MeasResultCLI_r16__Type ;
}.
Definition MeasResults__ext2O__list := (
 Opt MeasResultForRSSI_r16__Type MeasResultForRSSI_r16__cond ::
 Opt LocationInfo_r16__Type LocationInfo_r16__cond ::
 Opt UL_PDCP_DelayValueResultList_r16__Type UL_PDCP_DelayValueResultList_r16__cond ::
 Opt MeasResultsSL_r16__Type MeasResultsSL_r16__cond ::
 Opt MeasResultCLI_r16__Type MeasResultCLI_r16__cond ::
 nil).
Definition MeasResults__ext2O__cond z := 
  opt_cond MeasResultForRSSI_r16__cond (MeasResults__ext2O__measResultForRSSI_r16 z) /\
  opt_cond LocationInfo_r16__cond (MeasResults__ext2O__locationInfo_r16 z) /\
  opt_cond UL_PDCP_DelayValueResultList_r16__cond (MeasResults__ext2O__ul_PDCP_DelayValueResultList_r16 z) /\
  opt_cond MeasResultsSL_r16__cond (MeasResults__ext2O__measResultsSL_r16 z) /\
  opt_cond MeasResultCLI_r16__cond (MeasResults__ext2O__measResultCLI_r16 z) /\
  True.

Definition MeasResults__ext2__Type := MeasResults__ext2O__Type.
Definition MeasResults__ext2__cond := MeasResults__ext2O__cond.

Require Import NR.MeasResultRxTxTimeDiff_r17.

Opaque MeasResultRxTxTimeDiff_r17__cond MeasResultRxTxTimeDiff_r17__Format.

Require Import NR.UL_PDCP_ExcessDelayResultList_r17.

Opaque UL_PDCP_ExcessDelayResultList_r17__cond UL_PDCP_ExcessDelayResultList_r17__Format.

Record MeasResults__ext3O__Type : Set :=
  make__MeasResults__ext3O__Type {
    MeasResults__ext3O__measResultRxTxTimeDiff_r17 : option MeasResultRxTxTimeDiff_r17__Type ;
    MeasResults__ext3O__sl_MeasResultServingRelay_r17 : option octet_string ;
    MeasResults__ext3O__ul_PDCP_ExcessDelayResultList_r17 : option UL_PDCP_ExcessDelayResultList_r17__Type ;
    MeasResults__ext3O__coarseLocationInfo_r17 : option octet_string ;
}.
Definition MeasResults__ext3O__list := (
 Opt MeasResultRxTxTimeDiff_r17__Type MeasResultRxTxTimeDiff_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UL_PDCP_ExcessDelayResultList_r17__Type UL_PDCP_ExcessDelayResultList_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition MeasResults__ext3O__cond z := 
  opt_cond MeasResultRxTxTimeDiff_r17__cond (MeasResults__ext3O__measResultRxTxTimeDiff_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MeasResults__ext3O__sl_MeasResultServingRelay_r17 z) /\
  opt_cond UL_PDCP_ExcessDelayResultList_r17__cond (MeasResults__ext3O__ul_PDCP_ExcessDelayResultList_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MeasResults__ext3O__coarseLocationInfo_r17 z) /\
  True.

Definition MeasResults__ext3__Type := MeasResults__ext3O__Type.
Definition MeasResults__ext3__cond := MeasResults__ext3O__cond.

Record MeasResults__Type : Set :=
  make__MeasResults__Type {
    MeasResults__measId : MeasId__Type ;
    MeasResults__measResultServingMOList : MeasResultServMOList__Type ;
    MeasResults__measResultNeighCells : option MeasResults__measResultNeighCells__Type ;
    MeasResults__ext0 : option MeasResults__ext0__Type ;
    MeasResults__ext1 : option MeasResults__ext1__Type ;
    MeasResults__ext2 : option MeasResults__ext2__Type ;
    MeasResults__ext3 : option MeasResults__ext3__Type ;
}.
Definition MeasResults__root_list : list seq_elem := (
 Nor MeasId__Type MeasId__cond ::
 Nor MeasResultServMOList__Type MeasResultServMOList__cond ::
 Opt MeasResults__measResultNeighCells__Type MeasResults__measResultNeighCells__cond ::
 nil).
Definition MeasResults__ext_list : list typ := (
  typ_cons MeasResults__ext0__Type MeasResults__ext0__cond ::
  typ_cons MeasResults__ext1__Type MeasResults__ext1__cond ::
  typ_cons MeasResults__ext2__Type MeasResults__ext2__cond ::
  typ_cons MeasResults__ext3__Type MeasResults__ext3__cond ::
  nil).
Definition MeasResults__cond (z : MeasResults__Type) := 
(  MeasId__cond (MeasResults__measId z) /\
  MeasResultServMOList__cond (MeasResults__measResultServingMOList z) /\
  opt_cond MeasResults__measResultNeighCells__cond (MeasResults__measResultNeighCells z) /\
  True) /\ 
(  opt_cond MeasResults__ext0__cond (MeasResults__ext0 z) /\
  opt_cond MeasResults__ext1__cond (MeasResults__ext1 z) /\
  opt_cond MeasResults__ext2__cond (MeasResults__ext2 z) /\
  opt_cond MeasResults__ext3__cond (MeasResults__ext3 z) /\
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
Definition MeasResults__measResultNeighCells__root__F1 (z : MeasResults__measResultNeighCells__root__Type) : MeasResultListNR__Type := 
  match z with
  | MeasResults__measResultNeighCells__root__measResultListNR t => t
  end.
Definition MeasResults__measResultNeighCells__root__F2 (y : MeasResultListNR__Type) : MeasResults__measResultNeighCells__root__Type := MeasResults__measResultNeighCells__root__measResultListNR y.

Definition MeasResults__measResultNeighCells__root__helper2 : (forall z : MeasResults__measResultNeighCells__root__Type, MeasResults__measResultNeighCells__root__cond z -> MeasResultListNR__cond (MeasResults__measResultNeighCells__root__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition MeasResults__measResultNeighCells__root__helper3 : (forall z : MeasResults__measResultNeighCells__root__Type, MeasResults__measResultNeighCells__root__F2 (MeasResults__measResultNeighCells__root__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition MeasResults__measResultNeighCells__root__helper4 : (forall y : MeasResultListNR__Type, MeasResultListNR__cond y -> MeasResults__measResultNeighCells__root__cond (MeasResults__measResultNeighCells__root__F2 y) /\  MeasResults__measResultNeighCells__root__F1 (MeasResults__measResultNeighCells__root__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition MeasResults__measResultNeighCells__root__Format : T_Format MeasResults__measResultNeighCells__root__Type MeasResults__measResultNeighCells__root__cond :=
  proj2_format MeasResults__measResultNeighCells__root__cond MeasResultListNR__Format MeasResults__measResultNeighCells__root__F1 MeasResults__measResultNeighCells__root__F2 MeasResults__measResultNeighCells__root__helper2 MeasResults__measResultNeighCells__root__helper3 MeasResults__measResultNeighCells__root__helper4.
Opaque MeasResults__measResultNeighCells__root__cond MeasResults__measResultNeighCells__root__Format.


Definition MeasResults__measResultNeighCells__ext__Format_Type := Eval cbn in get_formats MeasResults__measResultNeighCells__ext__list.
Definition MeasResults__measResultNeighCells__ext__Format_list : MeasResults__measResultNeighCells__ext__Format_Type :=
  (MeasResultListEUTRA__Format, (MeasResultListUTRA_FDD_r16__Format, (octet_string_nc__Format, unit__Format))).
Definition MeasResults__measResultNeighCells__ext__list__Format := Eval compute in choice_ext_format MeasResults__measResultNeighCells__ext__list MeasResults__measResultNeighCells__ext__Format_list.
Definition MeasResults__measResultNeighCells__ext__F1 (z : MeasResults__measResultNeighCells__ext__Type) : (choice MeasResults__measResultNeighCells__ext__list) :=
  match z with
   | MeasResults__measResultNeighCells__ext__measResultListEUTRA t => existT _ 0 t
  | MeasResults__measResultNeighCells__ext__measResultListUTRA_FDD_r16 t => existT _ 1 t
  | MeasResults__measResultNeighCells__ext__sl_MeasResultsCandRelay_r17 t => existT _ 2 t
  end.
Definition MeasResults__measResultNeighCells__ext__g := (fun n => typ_set (get_nth_typ MeasResults__measResultNeighCells__ext__list n)).
Definition MeasResults__measResultNeighCells__ext__F2 (y : choice MeasResults__measResultNeighCells__ext__list) : MeasResults__measResultNeighCells__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasResults__measResultNeighCells__ext__g n -> MeasResults__measResultNeighCells__ext__Type) with
    | 0 => fun (t : MeasResultListEUTRA__Type) => MeasResults__measResultNeighCells__ext__measResultListEUTRA t 
    | 1 => fun (t : MeasResultListUTRA_FDD_r16__Type) => MeasResults__measResultNeighCells__ext__measResultListUTRA_FDD_r16 t 
    | 2 => fun (t : octet_string) => MeasResults__measResultNeighCells__ext__sl_MeasResultsCandRelay_r17 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : MeasResults__measResultNeighCells__ext__g (S (S (S x')))) =>let t' :=
                       eq_rect (get_nth_typ MeasResults__measResultNeighCells__ext__list (S (S (S x'))))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len MeasResults__measResultNeighCells__ext__list (S (S (S x')))
                       (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return MeasResults__measResultNeighCells__ext__Type with end) n0
                       end t0).

Lemma MeasResults__measResultNeighCells__ext__helper2 :  forall (y : MeasResults__measResultNeighCells__ext__Type), MeasResults__measResultNeighCells__ext__cond y -> choice_cond MeasResults__measResultNeighCells__ext__list (MeasResults__measResultNeighCells__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasResults__measResultNeighCells__ext__helper3 :  forall (y : MeasResults__measResultNeighCells__ext__Type), MeasResults__measResultNeighCells__ext__F2 (MeasResults__measResultNeighCells__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasResults__measResultNeighCells__ext__helper4 : (forall b : choice MeasResults__measResultNeighCells__ext__list, choice_cond MeasResults__measResultNeighCells__ext__list b -> MeasResults__measResultNeighCells__ext__cond (MeasResults__measResultNeighCells__ext__F2 b) /\ MeasResults__measResultNeighCells__ext__F1 (MeasResults__measResultNeighCells__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasResults__measResultNeighCells__ext__F1 MeasResults__measResultNeighCells__ext__F2.
Definition MeasResults__measResultNeighCells__ext__Format : T_Format MeasResults__measResultNeighCells__ext__Type MeasResults__measResultNeighCells__ext__cond :=
          proj2_format MeasResults__measResultNeighCells__ext__cond MeasResults__measResultNeighCells__ext__list__Format MeasResults__measResultNeighCells__ext__F1 MeasResults__measResultNeighCells__ext__F2 MeasResults__measResultNeighCells__ext__helper2 MeasResults__measResultNeighCells__ext__helper3 MeasResults__measResultNeighCells__ext__helper4.
Opaque MeasResults__measResultNeighCells__ext__cond MeasResults__measResultNeighCells__ext__Format.

Definition MeasResults__measResultNeighCells__Format : T_Format MeasResults__measResultNeighCells__Type MeasResults__measResultNeighCells__cond := sum_format MeasResults__measResultNeighCells__root__Format MeasResults__measResultNeighCells__ext__Format.
Opaque MeasResults__measResultNeighCells__cond MeasResults__measResultNeighCells__Format.


Definition MeasResults__ext0O__Format_Type := Eval cbn in seq_format_prod MeasResults__ext0O__list.
Definition MeasResults__ext0O__Format_list : MeasResults__ext0O__Format_Type :=
  (MeasResultServFreqListEUTRA_SCG__Format, (MeasResultServFreqListNR_SCG__Format, (MeasResultSFTD_EUTRA__Format, (MeasResultCellSFTD_NR__Format, unit_format)))).
Definition MeasResults__ext0O__list__Format := (*Eval compute in *) seq_format MeasResults__ext0O__list MeasResults__ext0O__Format_list.
Definition MeasResults__ext0O__F1 z :=
  (MeasResults__ext0O__measResultServFreqListEUTRA_SCG z, (MeasResults__ext0O__measResultServFreqListNR_SCG z, (MeasResults__ext0O__measResultSFTD_EUTRA z, (MeasResults__ext0O__measResultSFTD_NR z, tt)))).
Definition MeasResults__ext0O__F2 (y : seq_type MeasResults__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasResults__ext0O__Type i0 i1 i2 i3
  end.
Lemma MeasResults__ext0O__F1F2_cond (z : MeasResults__ext0O__Type)
  : MeasResults__ext0O__cond z ->
  (seq_cond MeasResults__ext0O__list (MeasResults__ext0O__F1 z)).
intro H. unfold MeasResults__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasResults__ext0O__F1F2_cond2 (z : MeasResults__ext0O__Type)
 : MeasResults__ext0O__F2 (MeasResults__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResults__ext0O__F2F1_cond (y : seq_type MeasResults__ext0O__list)
  : seq_cond MeasResults__ext0O__list y ->
 (MeasResults__ext0O__cond (MeasResults__ext0O__F2 y)) /\  MeasResults__ext0O__F1 (MeasResults__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResults__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasResults__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResults__ext0O__Format : T_Format MeasResults__ext0O__Type MeasResults__ext0O__cond :=
        proj2_format  MeasResults__ext0O__cond MeasResults__ext0O__list__Format
    MeasResults__ext0O__F1 MeasResults__ext0O__F2 MeasResults__ext0O__F1F2_cond  MeasResults__ext0O__F1F2_cond2 MeasResults__ext0O__F2F1_cond.
Opaque MeasResults__ext0O__cond MeasResults__ext0O__Format.

Definition MeasResults__ext0__check_all_none (b : MeasResults__ext0O__Type) : bool :=
match b with 
  | make__MeasResults__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition MeasResults__ext0__Format : T_Format MeasResults__ext0__Type MeasResults__ext0__cond :=
  restrict_add_format MeasResults__ext0__check_all_none MeasResults__ext0O__Format.

Opaque MeasResults__ext0__cond MeasResults__ext0__Format.


Definition MeasResults__ext1O__Format_Type := Eval cbn in seq_format_prod MeasResults__ext1O__list.
Definition MeasResults__ext1O__Format_list : MeasResults__ext1O__Format_Type :=
  (MeasResultCellListSFTD_NR__Format, unit_format).
Definition MeasResults__ext1O__list__Format := (*Eval compute in *) seq_format MeasResults__ext1O__list MeasResults__ext1O__Format_list.
Definition MeasResults__ext1O__F1 z :=
  (MeasResults__ext1O__measResultCellListSFTD_NR z, tt).
Definition MeasResults__ext1O__F2 (y : seq_type MeasResults__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__MeasResults__ext1O__Type i0
  end.
Lemma MeasResults__ext1O__F1F2_cond (z : MeasResults__ext1O__Type)
  : MeasResults__ext1O__cond z ->
  (seq_cond MeasResults__ext1O__list (MeasResults__ext1O__F1 z)).
intro H. unfold MeasResults__ext1O__cond in H. simpl. auto. Qed.
Lemma MeasResults__ext1O__F1F2_cond2 (z : MeasResults__ext1O__Type)
 : MeasResults__ext1O__F2 (MeasResults__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResults__ext1O__F2F1_cond (y : seq_type MeasResults__ext1O__list)
  : seq_cond MeasResults__ext1O__list y ->
 (MeasResults__ext1O__cond (MeasResults__ext1O__F2 y)) /\  MeasResults__ext1O__F1 (MeasResults__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResults__ext1O__cond. simpl in *. auto.
 - simpl. unfold MeasResults__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResults__ext1O__Format : T_Format MeasResults__ext1O__Type MeasResults__ext1O__cond :=
        proj2_format  MeasResults__ext1O__cond MeasResults__ext1O__list__Format
    MeasResults__ext1O__F1 MeasResults__ext1O__F2 MeasResults__ext1O__F1F2_cond  MeasResults__ext1O__F1F2_cond2 MeasResults__ext1O__F2F1_cond.
Opaque MeasResults__ext1O__cond MeasResults__ext1O__Format.

Definition MeasResults__ext1__check_all_none (b : MeasResults__ext1O__Type) : bool :=
match b with 
  | make__MeasResults__ext1O__Type None  => false 
  | _ => true 
 end.
Definition MeasResults__ext1__Format : T_Format MeasResults__ext1__Type MeasResults__ext1__cond :=
  restrict_add_format MeasResults__ext1__check_all_none MeasResults__ext1O__Format.

Opaque MeasResults__ext1__cond MeasResults__ext1__Format.


Definition MeasResults__ext2O__Format_Type := Eval cbn in seq_format_prod MeasResults__ext2O__list.
Definition MeasResults__ext2O__Format_list : MeasResults__ext2O__Format_Type :=
  (MeasResultForRSSI_r16__Format, (LocationInfo_r16__Format, (UL_PDCP_DelayValueResultList_r16__Format, (MeasResultsSL_r16__Format, (MeasResultCLI_r16__Format, unit_format))))).
Definition MeasResults__ext2O__list__Format := (*Eval compute in *) seq_format MeasResults__ext2O__list MeasResults__ext2O__Format_list.
Definition MeasResults__ext2O__F1 z :=
  (MeasResults__ext2O__measResultForRSSI_r16 z, (MeasResults__ext2O__locationInfo_r16 z, (MeasResults__ext2O__ul_PDCP_DelayValueResultList_r16 z, (MeasResults__ext2O__measResultsSL_r16 z, (MeasResults__ext2O__measResultCLI_r16 z, tt))))).
Definition MeasResults__ext2O__F2 (y : seq_type MeasResults__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__MeasResults__ext2O__Type i0 i1 i2 i3 i4
  end.
Lemma MeasResults__ext2O__F1F2_cond (z : MeasResults__ext2O__Type)
  : MeasResults__ext2O__cond z ->
  (seq_cond MeasResults__ext2O__list (MeasResults__ext2O__F1 z)).
intro H. unfold MeasResults__ext2O__cond in H. simpl. auto. Qed.
Lemma MeasResults__ext2O__F1F2_cond2 (z : MeasResults__ext2O__Type)
 : MeasResults__ext2O__F2 (MeasResults__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResults__ext2O__F2F1_cond (y : seq_type MeasResults__ext2O__list)
  : seq_cond MeasResults__ext2O__list y ->
 (MeasResults__ext2O__cond (MeasResults__ext2O__F2 y)) /\  MeasResults__ext2O__F1 (MeasResults__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResults__ext2O__cond. simpl in *. auto.
 - simpl. unfold MeasResults__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResults__ext2O__Format : T_Format MeasResults__ext2O__Type MeasResults__ext2O__cond :=
        proj2_format  MeasResults__ext2O__cond MeasResults__ext2O__list__Format
    MeasResults__ext2O__F1 MeasResults__ext2O__F2 MeasResults__ext2O__F1F2_cond  MeasResults__ext2O__F1F2_cond2 MeasResults__ext2O__F2F1_cond.
Opaque MeasResults__ext2O__cond MeasResults__ext2O__Format.

Definition MeasResults__ext2__check_all_none (b : MeasResults__ext2O__Type) : bool :=
match b with 
  | make__MeasResults__ext2O__Type None None None None None  => false 
  | _ => true 
 end.
Definition MeasResults__ext2__Format : T_Format MeasResults__ext2__Type MeasResults__ext2__cond :=
  restrict_add_format MeasResults__ext2__check_all_none MeasResults__ext2O__Format.

Opaque MeasResults__ext2__cond MeasResults__ext2__Format.


Definition MeasResults__ext3O__Format_Type := Eval cbn in seq_format_prod MeasResults__ext3O__list.
Definition MeasResults__ext3O__Format_list : MeasResults__ext3O__Format_Type :=
  (MeasResultRxTxTimeDiff_r17__Format, (octet_string_nc__Format, (UL_PDCP_ExcessDelayResultList_r17__Format, (octet_string_nc__Format, unit_format)))).
Definition MeasResults__ext3O__list__Format := (*Eval compute in *) seq_format MeasResults__ext3O__list MeasResults__ext3O__Format_list.
Definition MeasResults__ext3O__F1 z :=
  (MeasResults__ext3O__measResultRxTxTimeDiff_r17 z, (MeasResults__ext3O__sl_MeasResultServingRelay_r17 z, (MeasResults__ext3O__ul_PDCP_ExcessDelayResultList_r17 z, (MeasResults__ext3O__coarseLocationInfo_r17 z, tt)))).
Definition MeasResults__ext3O__F2 (y : seq_type MeasResults__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasResults__ext3O__Type i0 i1 i2 i3
  end.
Lemma MeasResults__ext3O__F1F2_cond (z : MeasResults__ext3O__Type)
  : MeasResults__ext3O__cond z ->
  (seq_cond MeasResults__ext3O__list (MeasResults__ext3O__F1 z)).
intro H. unfold MeasResults__ext3O__cond in H. simpl. auto. Qed.
Lemma MeasResults__ext3O__F1F2_cond2 (z : MeasResults__ext3O__Type)
 : MeasResults__ext3O__F2 (MeasResults__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResults__ext3O__F2F1_cond (y : seq_type MeasResults__ext3O__list)
  : seq_cond MeasResults__ext3O__list y ->
 (MeasResults__ext3O__cond (MeasResults__ext3O__F2 y)) /\  MeasResults__ext3O__F1 (MeasResults__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResults__ext3O__cond. simpl in *. auto.
 - simpl. unfold MeasResults__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResults__ext3O__Format : T_Format MeasResults__ext3O__Type MeasResults__ext3O__cond :=
        proj2_format  MeasResults__ext3O__cond MeasResults__ext3O__list__Format
    MeasResults__ext3O__F1 MeasResults__ext3O__F2 MeasResults__ext3O__F1F2_cond  MeasResults__ext3O__F1F2_cond2 MeasResults__ext3O__F2F1_cond.
Opaque MeasResults__ext3O__cond MeasResults__ext3O__Format.

Definition MeasResults__ext3__check_all_none (b : MeasResults__ext3O__Type) : bool :=
match b with 
  | make__MeasResults__ext3O__Type None None None None  => false 
  | _ => true 
 end.
Definition MeasResults__ext3__Format : T_Format MeasResults__ext3__Type MeasResults__ext3__cond :=
  restrict_add_format MeasResults__ext3__check_all_none MeasResults__ext3O__Format.

Opaque MeasResults__ext3__cond MeasResults__ext3__Format.


Definition MeasResults__root_Format_Type := Eval cbn in seq_format_prod MeasResults__root_list.
Definition MeasResults__root_Format_list : MeasResults__root_Format_Type :=
  (MeasId__Format, (MeasResultServMOList__Format, (MeasResults__measResultNeighCells__Format, unit_format))).

Definition MeasResults__ext_Format_Type := Eval cbn in get_formats MeasResults__ext_list.
Definition MeasResults__ext_Format_list : MeasResults__ext_Format_Type :=
  (MeasResults__ext0__Format, (MeasResults__ext1__Format, (MeasResults__ext2__Format, (MeasResults__ext3__Format, unit__Format)))).

Definition MeasResults__list_type : Set := (seq_type MeasResults__root_list) * (seq_ext_type MeasResults__ext_list).
Definition MeasResults__list_cond (z : MeasResults__list_type) : Prop :=
        (seq_cond MeasResults__root_list (fst z)) /\ (seq_ext_cond MeasResults__ext_list (snd z)).
Definition MeasResults__list_format : T_Format MeasResults__list_type MeasResults__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResults__root_list MeasResults__root_Format_list MeasResults__ext_list MeasResults__ext_Format_list.

Opaque MeasResults__list_format.
Definition MeasResults__F1 (z : MeasResults__Type) : MeasResults__list_type :=
  (((MeasResults__measId z, (MeasResults__measResultServingMOList z, (MeasResults__measResultNeighCells z, tt)))), (
(MeasResults__ext0 z, (MeasResults__ext1 z, (MeasResults__ext2 z, (MeasResults__ext3 z, tt)))))).
Definition MeasResults__F2 (y : MeasResults__list_type) : MeasResults__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, (i3, _)))))=>
    make__MeasResults__Type j0 j1 j2 i0 i1 i2 i3
  end.
Definition MeasResults__helper1 : (forall a : MeasResults__Type, MeasResults__cond a -> MeasResults__list_cond (MeasResults__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResults__helper2 : (forall a : MeasResults__Type, MeasResults__F2 (MeasResults__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResults__helper3 : (forall b : MeasResults__list_type, MeasResults__list_cond b -> MeasResults__cond (MeasResults__F2 b) /\ MeasResults__F1 (MeasResults__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResults__cond, MeasResults__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResults__Format : T_Format MeasResults__Type MeasResults__cond :=
 proj2_format MeasResults__cond MeasResults__list_format  MeasResults__F1 MeasResults__F2 MeasResults__helper1 MeasResults__helper2 MeasResults__helper3.

Opaque MeasResults__cond MeasResults__Format.

