Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SSB_ToMeasure.
Definition SSB_ConfigMobility__ssb_ToMeasure__Type := SetupRelease__Type SSB_ToMeasure__Type.
Definition SSB_ConfigMobility__ssb_ToMeasure__cond := SetupRelease__cond _ SSB_ToMeasure__cond.
Definition SSB_ConfigMobility__ssb_ToMeasure__Format : T_Format SSB_ConfigMobility__ssb_ToMeasure__Type SSB_ConfigMobility__ssb_ToMeasure__cond := SetupRelease__Format _ _ SSB_ToMeasure__Format.
Opaque SSB_ConfigMobility__ssb_ToMeasure__cond SSB_ConfigMobility__ssb_ToMeasure__Format.

Require Import NR.SS_RSSI_Measurement.

Opaque SS_RSSI_Measurement__cond SS_RSSI_Measurement__Format.

Require Import NR.SSB_PositionQCL_Relation_r16.

Opaque SSB_PositionQCL_Relation_r16__cond SSB_PositionQCL_Relation_r16__Format.

Require Import NR.SSB_PositionQCL_CellsToAddModList_r16.

Opaque SSB_PositionQCL_CellsToAddModList_r16__cond SSB_PositionQCL_CellsToAddModList_r16__Format.

Require Import NR.PCI_List.

Opaque PCI_List__cond PCI_List__Format.

Record SSB_ConfigMobility__ext0O__Type : Set :=
  make__SSB_ConfigMobility__ext0O__Type {
    SSB_ConfigMobility__ext0O__ssb_PositionQCL_Common_r16 : option SSB_PositionQCL_Relation_r16__Type ;
    SSB_ConfigMobility__ext0O__ssb_PositionQCL_CellsToAddModList_r16 : option SSB_PositionQCL_CellsToAddModList_r16__Type ;
    SSB_ConfigMobility__ext0O__ssb_PositionQCL_CellsToRemoveList_r16 : option PCI_List__Type ;
}.
Definition SSB_ConfigMobility__ext0O__list := (
 Opt SSB_PositionQCL_Relation_r16__Type SSB_PositionQCL_Relation_r16__cond ::
 Opt SSB_PositionQCL_CellsToAddModList_r16__Type SSB_PositionQCL_CellsToAddModList_r16__cond ::
 Opt PCI_List__Type PCI_List__cond ::
 nil).
Definition SSB_ConfigMobility__ext0O__cond z := 
  opt_cond SSB_PositionQCL_Relation_r16__cond (SSB_ConfigMobility__ext0O__ssb_PositionQCL_Common_r16 z) /\
  opt_cond SSB_PositionQCL_CellsToAddModList_r16__cond (SSB_ConfigMobility__ext0O__ssb_PositionQCL_CellsToAddModList_r16 z) /\
  opt_cond PCI_List__cond (SSB_ConfigMobility__ext0O__ssb_PositionQCL_CellsToRemoveList_r16 z) /\
  True.

Definition SSB_ConfigMobility__ext0__Type := SSB_ConfigMobility__ext0O__Type.
Definition SSB_ConfigMobility__ext0__cond := SSB_ConfigMobility__ext0O__cond.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.SSB_PositionQCL_Relation_r17.

Opaque SSB_PositionQCL_Relation_r17__cond SSB_PositionQCL_Relation_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SSB_PositionQCL_CellList_r17.
Definition SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__Type := SetupRelease__Type SSB_PositionQCL_CellList_r17__Type.
Definition SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__cond := SetupRelease__cond _ SSB_PositionQCL_CellList_r17__cond.
Definition SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__Format : T_Format SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__Type SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__cond := SetupRelease__Format _ _ SSB_PositionQCL_CellList_r17__Format.
Opaque SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__cond SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__Format.

Record SSB_ConfigMobility__ext1O__Type : Set :=
  make__SSB_ConfigMobility__ext1O__Type {
    SSB_ConfigMobility__ext1O__deriveSSB_IndexFromCellInter_r17 : option ServCellIndex__Type ;
    SSB_ConfigMobility__ext1O__ssb_PositionQCL_Common_r17 : option SSB_PositionQCL_Relation_r17__Type ;
    SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17 : option SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__Type ;
}.
Definition SSB_ConfigMobility__ext1O__list := (
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Opt SSB_PositionQCL_Relation_r17__Type SSB_PositionQCL_Relation_r17__cond ::
 Opt SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__Type SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__cond ::
 nil).
Definition SSB_ConfigMobility__ext1O__cond z := 
  opt_cond ServCellIndex__cond (SSB_ConfigMobility__ext1O__deriveSSB_IndexFromCellInter_r17 z) /\
  opt_cond SSB_PositionQCL_Relation_r17__cond (SSB_ConfigMobility__ext1O__ssb_PositionQCL_Common_r17 z) /\
  opt_cond SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__cond (SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17 z) /\
  True.

Definition SSB_ConfigMobility__ext1__Type := SSB_ConfigMobility__ext1O__Type.
Definition SSB_ConfigMobility__ext1__cond := SSB_ConfigMobility__ext1O__cond.

Require Import NR.PCI_List.

Opaque PCI_List__cond PCI_List__Format.

Require Import NR.PCI_List.

Opaque PCI_List__cond PCI_List__Format.

Record SSB_ConfigMobility__ext2O__Type : Set :=
  make__SSB_ConfigMobility__ext2O__Type {
    SSB_ConfigMobility__ext2O__cca_CellsToAddModList_r17 : option PCI_List__Type ;
    SSB_ConfigMobility__ext2O__cca_CellsToRemoveList_r17 : option PCI_List__Type ;
}.
Definition SSB_ConfigMobility__ext2O__list := (
 Opt PCI_List__Type PCI_List__cond ::
 Opt PCI_List__Type PCI_List__cond ::
 nil).
Definition SSB_ConfigMobility__ext2O__cond z := 
  opt_cond PCI_List__cond (SSB_ConfigMobility__ext2O__cca_CellsToAddModList_r17 z) /\
  opt_cond PCI_List__cond (SSB_ConfigMobility__ext2O__cca_CellsToRemoveList_r17 z) /\
  True.

Definition SSB_ConfigMobility__ext2__Type := SSB_ConfigMobility__ext2O__Type.
Definition SSB_ConfigMobility__ext2__cond := SSB_ConfigMobility__ext2O__cond.

Record SSB_ConfigMobility__Type : Set :=
  make__SSB_ConfigMobility__Type {
    SSB_ConfigMobility__ssb_ToMeasure : option SSB_ConfigMobility__ssb_ToMeasure__Type ;
    SSB_ConfigMobility__deriveSSB_IndexFromCell : bool ;
    SSB_ConfigMobility__ss_RSSI_Measurement : option SS_RSSI_Measurement__Type ;
    SSB_ConfigMobility__ext0 : option SSB_ConfigMobility__ext0__Type ;
    SSB_ConfigMobility__ext1 : option SSB_ConfigMobility__ext1__Type ;
    SSB_ConfigMobility__ext2 : option SSB_ConfigMobility__ext2__Type ;
}.
Definition SSB_ConfigMobility__root_list : list seq_elem := (
 Opt SSB_ConfigMobility__ssb_ToMeasure__Type SSB_ConfigMobility__ssb_ToMeasure__cond ::
 Nor bool (fun _ => True) ::
 Opt SS_RSSI_Measurement__Type SS_RSSI_Measurement__cond ::
 nil).
Definition SSB_ConfigMobility__ext_list : list typ := (
  typ_cons SSB_ConfigMobility__ext0__Type SSB_ConfigMobility__ext0__cond ::
  typ_cons SSB_ConfigMobility__ext1__Type SSB_ConfigMobility__ext1__cond ::
  typ_cons SSB_ConfigMobility__ext2__Type SSB_ConfigMobility__ext2__cond ::
  nil).
Definition SSB_ConfigMobility__cond (z : SSB_ConfigMobility__Type) := 
(  opt_cond SSB_ConfigMobility__ssb_ToMeasure__cond (SSB_ConfigMobility__ssb_ToMeasure z) /\
  (fun _ => True) (SSB_ConfigMobility__deriveSSB_IndexFromCell z) /\
  opt_cond SS_RSSI_Measurement__cond (SSB_ConfigMobility__ss_RSSI_Measurement z) /\
  True) /\ 
(  opt_cond SSB_ConfigMobility__ext0__cond (SSB_ConfigMobility__ext0 z) /\
  opt_cond SSB_ConfigMobility__ext1__cond (SSB_ConfigMobility__ext1 z) /\
  opt_cond SSB_ConfigMobility__ext2__cond (SSB_ConfigMobility__ext2 z) /\
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
Opaque SSB_ConfigMobility__ssb_ToMeasure__cond SSB_ConfigMobility__ssb_ToMeasure__Format.


Definition SSB_ConfigMobility__ext0O__Format_Type := Eval cbn in seq_format_prod SSB_ConfigMobility__ext0O__list.
Definition SSB_ConfigMobility__ext0O__Format_list : SSB_ConfigMobility__ext0O__Format_Type :=
  (SSB_PositionQCL_Relation_r16__Format, (SSB_PositionQCL_CellsToAddModList_r16__Format, (PCI_List__Format, unit_format))).
Definition SSB_ConfigMobility__ext0O__list__Format := (*Eval compute in *) seq_format SSB_ConfigMobility__ext0O__list SSB_ConfigMobility__ext0O__Format_list.
Definition SSB_ConfigMobility__ext0O__F1 z :=
  (SSB_ConfigMobility__ext0O__ssb_PositionQCL_Common_r16 z, (SSB_ConfigMobility__ext0O__ssb_PositionQCL_CellsToAddModList_r16 z, (SSB_ConfigMobility__ext0O__ssb_PositionQCL_CellsToRemoveList_r16 z, tt))).
Definition SSB_ConfigMobility__ext0O__F2 (y : seq_type SSB_ConfigMobility__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SSB_ConfigMobility__ext0O__Type i0 i1 i2
  end.
Lemma SSB_ConfigMobility__ext0O__F1F2_cond (z : SSB_ConfigMobility__ext0O__Type)
  : SSB_ConfigMobility__ext0O__cond z ->
  (seq_cond SSB_ConfigMobility__ext0O__list (SSB_ConfigMobility__ext0O__F1 z)).
intro H. unfold SSB_ConfigMobility__ext0O__cond in H. simpl. auto. Qed.
Lemma SSB_ConfigMobility__ext0O__F1F2_cond2 (z : SSB_ConfigMobility__ext0O__Type)
 : SSB_ConfigMobility__ext0O__F2 (SSB_ConfigMobility__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_ConfigMobility__ext0O__F2F1_cond (y : seq_type SSB_ConfigMobility__ext0O__list)
  : seq_cond SSB_ConfigMobility__ext0O__list y ->
 (SSB_ConfigMobility__ext0O__cond (SSB_ConfigMobility__ext0O__F2 y)) /\  SSB_ConfigMobility__ext0O__F1 (SSB_ConfigMobility__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_ConfigMobility__ext0O__cond. simpl in *. auto.
 - simpl. unfold SSB_ConfigMobility__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_ConfigMobility__ext0O__Format : T_Format SSB_ConfigMobility__ext0O__Type SSB_ConfigMobility__ext0O__cond :=
        proj2_format  SSB_ConfigMobility__ext0O__cond SSB_ConfigMobility__ext0O__list__Format
    SSB_ConfigMobility__ext0O__F1 SSB_ConfigMobility__ext0O__F2 SSB_ConfigMobility__ext0O__F1F2_cond  SSB_ConfigMobility__ext0O__F1F2_cond2 SSB_ConfigMobility__ext0O__F2F1_cond.
Opaque SSB_ConfigMobility__ext0O__cond SSB_ConfigMobility__ext0O__Format.

Definition SSB_ConfigMobility__ext0__check_all_none (b : SSB_ConfigMobility__ext0O__Type) : bool :=
match b with 
  | make__SSB_ConfigMobility__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition SSB_ConfigMobility__ext0__Format : T_Format SSB_ConfigMobility__ext0__Type SSB_ConfigMobility__ext0__cond :=
  restrict_add_format SSB_ConfigMobility__ext0__check_all_none SSB_ConfigMobility__ext0O__Format.

Opaque SSB_ConfigMobility__ext0__cond SSB_ConfigMobility__ext0__Format.

Opaque SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__cond SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__Format.


Definition SSB_ConfigMobility__ext1O__Format_Type := Eval cbn in seq_format_prod SSB_ConfigMobility__ext1O__list.
Definition SSB_ConfigMobility__ext1O__Format_list : SSB_ConfigMobility__ext1O__Format_Type :=
  (ServCellIndex__Format, (SSB_PositionQCL_Relation_r17__Format, (SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17__Format, unit_format))).
Definition SSB_ConfigMobility__ext1O__list__Format := (*Eval compute in *) seq_format SSB_ConfigMobility__ext1O__list SSB_ConfigMobility__ext1O__Format_list.
Definition SSB_ConfigMobility__ext1O__F1 z :=
  (SSB_ConfigMobility__ext1O__deriveSSB_IndexFromCellInter_r17 z, (SSB_ConfigMobility__ext1O__ssb_PositionQCL_Common_r17 z, (SSB_ConfigMobility__ext1O__ssb_PositionQCL_Cells_r17 z, tt))).
Definition SSB_ConfigMobility__ext1O__F2 (y : seq_type SSB_ConfigMobility__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SSB_ConfigMobility__ext1O__Type i0 i1 i2
  end.
Lemma SSB_ConfigMobility__ext1O__F1F2_cond (z : SSB_ConfigMobility__ext1O__Type)
  : SSB_ConfigMobility__ext1O__cond z ->
  (seq_cond SSB_ConfigMobility__ext1O__list (SSB_ConfigMobility__ext1O__F1 z)).
intro H. unfold SSB_ConfigMobility__ext1O__cond in H. simpl. auto. Qed.
Lemma SSB_ConfigMobility__ext1O__F1F2_cond2 (z : SSB_ConfigMobility__ext1O__Type)
 : SSB_ConfigMobility__ext1O__F2 (SSB_ConfigMobility__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_ConfigMobility__ext1O__F2F1_cond (y : seq_type SSB_ConfigMobility__ext1O__list)
  : seq_cond SSB_ConfigMobility__ext1O__list y ->
 (SSB_ConfigMobility__ext1O__cond (SSB_ConfigMobility__ext1O__F2 y)) /\  SSB_ConfigMobility__ext1O__F1 (SSB_ConfigMobility__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_ConfigMobility__ext1O__cond. simpl in *. auto.
 - simpl. unfold SSB_ConfigMobility__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_ConfigMobility__ext1O__Format : T_Format SSB_ConfigMobility__ext1O__Type SSB_ConfigMobility__ext1O__cond :=
        proj2_format  SSB_ConfigMobility__ext1O__cond SSB_ConfigMobility__ext1O__list__Format
    SSB_ConfigMobility__ext1O__F1 SSB_ConfigMobility__ext1O__F2 SSB_ConfigMobility__ext1O__F1F2_cond  SSB_ConfigMobility__ext1O__F1F2_cond2 SSB_ConfigMobility__ext1O__F2F1_cond.
Opaque SSB_ConfigMobility__ext1O__cond SSB_ConfigMobility__ext1O__Format.

Definition SSB_ConfigMobility__ext1__check_all_none (b : SSB_ConfigMobility__ext1O__Type) : bool :=
match b with 
  | make__SSB_ConfigMobility__ext1O__Type None None None  => false 
  | _ => true 
 end.
Definition SSB_ConfigMobility__ext1__Format : T_Format SSB_ConfigMobility__ext1__Type SSB_ConfigMobility__ext1__cond :=
  restrict_add_format SSB_ConfigMobility__ext1__check_all_none SSB_ConfigMobility__ext1O__Format.

Opaque SSB_ConfigMobility__ext1__cond SSB_ConfigMobility__ext1__Format.


Definition SSB_ConfigMobility__ext2O__Format_Type := Eval cbn in seq_format_prod SSB_ConfigMobility__ext2O__list.
Definition SSB_ConfigMobility__ext2O__Format_list : SSB_ConfigMobility__ext2O__Format_Type :=
  (PCI_List__Format, (PCI_List__Format, unit_format)).
Definition SSB_ConfigMobility__ext2O__list__Format := (*Eval compute in *) seq_format SSB_ConfigMobility__ext2O__list SSB_ConfigMobility__ext2O__Format_list.
Definition SSB_ConfigMobility__ext2O__F1 z :=
  (SSB_ConfigMobility__ext2O__cca_CellsToAddModList_r17 z, (SSB_ConfigMobility__ext2O__cca_CellsToRemoveList_r17 z, tt)).
Definition SSB_ConfigMobility__ext2O__F2 (y : seq_type SSB_ConfigMobility__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SSB_ConfigMobility__ext2O__Type i0 i1
  end.
Lemma SSB_ConfigMobility__ext2O__F1F2_cond (z : SSB_ConfigMobility__ext2O__Type)
  : SSB_ConfigMobility__ext2O__cond z ->
  (seq_cond SSB_ConfigMobility__ext2O__list (SSB_ConfigMobility__ext2O__F1 z)).
intro H. unfold SSB_ConfigMobility__ext2O__cond in H. simpl. auto. Qed.
Lemma SSB_ConfigMobility__ext2O__F1F2_cond2 (z : SSB_ConfigMobility__ext2O__Type)
 : SSB_ConfigMobility__ext2O__F2 (SSB_ConfigMobility__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_ConfigMobility__ext2O__F2F1_cond (y : seq_type SSB_ConfigMobility__ext2O__list)
  : seq_cond SSB_ConfigMobility__ext2O__list y ->
 (SSB_ConfigMobility__ext2O__cond (SSB_ConfigMobility__ext2O__F2 y)) /\  SSB_ConfigMobility__ext2O__F1 (SSB_ConfigMobility__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_ConfigMobility__ext2O__cond. simpl in *. auto.
 - simpl. unfold SSB_ConfigMobility__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_ConfigMobility__ext2O__Format : T_Format SSB_ConfigMobility__ext2O__Type SSB_ConfigMobility__ext2O__cond :=
        proj2_format  SSB_ConfigMobility__ext2O__cond SSB_ConfigMobility__ext2O__list__Format
    SSB_ConfigMobility__ext2O__F1 SSB_ConfigMobility__ext2O__F2 SSB_ConfigMobility__ext2O__F1F2_cond  SSB_ConfigMobility__ext2O__F1F2_cond2 SSB_ConfigMobility__ext2O__F2F1_cond.
Opaque SSB_ConfigMobility__ext2O__cond SSB_ConfigMobility__ext2O__Format.

Definition SSB_ConfigMobility__ext2__check_all_none (b : SSB_ConfigMobility__ext2O__Type) : bool :=
match b with 
  | make__SSB_ConfigMobility__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition SSB_ConfigMobility__ext2__Format : T_Format SSB_ConfigMobility__ext2__Type SSB_ConfigMobility__ext2__cond :=
  restrict_add_format SSB_ConfigMobility__ext2__check_all_none SSB_ConfigMobility__ext2O__Format.

Opaque SSB_ConfigMobility__ext2__cond SSB_ConfigMobility__ext2__Format.


Definition SSB_ConfigMobility__root_Format_Type := Eval cbn in seq_format_prod SSB_ConfigMobility__root_list.
Definition SSB_ConfigMobility__root_Format_list : SSB_ConfigMobility__root_Format_Type :=
  (SSB_ConfigMobility__ssb_ToMeasure__Format, (bool__Format, (SS_RSSI_Measurement__Format, unit_format))).

Definition SSB_ConfigMobility__ext_Format_Type := Eval cbn in get_formats SSB_ConfigMobility__ext_list.
Definition SSB_ConfigMobility__ext_Format_list : SSB_ConfigMobility__ext_Format_Type :=
  (SSB_ConfigMobility__ext0__Format, (SSB_ConfigMobility__ext1__Format, (SSB_ConfigMobility__ext2__Format, unit__Format))).

Definition SSB_ConfigMobility__list_type : Set := (seq_type SSB_ConfigMobility__root_list) * (seq_ext_type SSB_ConfigMobility__ext_list).
Definition SSB_ConfigMobility__list_cond (z : SSB_ConfigMobility__list_type) : Prop :=
        (seq_cond SSB_ConfigMobility__root_list (fst z)) /\ (seq_ext_cond SSB_ConfigMobility__ext_list (snd z)).
Definition SSB_ConfigMobility__list_format : T_Format SSB_ConfigMobility__list_type SSB_ConfigMobility__list_cond :=
 (* Eval compute in *) seq_ext_format SSB_ConfigMobility__root_list SSB_ConfigMobility__root_Format_list SSB_ConfigMobility__ext_list SSB_ConfigMobility__ext_Format_list.

Opaque SSB_ConfigMobility__list_format.
Definition SSB_ConfigMobility__F1 (z : SSB_ConfigMobility__Type) : SSB_ConfigMobility__list_type :=
  (((SSB_ConfigMobility__ssb_ToMeasure z, (SSB_ConfigMobility__deriveSSB_IndexFromCell z, (SSB_ConfigMobility__ss_RSSI_Measurement z, tt)))), (
(SSB_ConfigMobility__ext0 z, (SSB_ConfigMobility__ext1 z, (SSB_ConfigMobility__ext2 z, tt))))).
Definition SSB_ConfigMobility__F2 (y : SSB_ConfigMobility__list_type) : SSB_ConfigMobility__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, _))))=>
    make__SSB_ConfigMobility__Type j0 j1 j2 i0 i1 i2
  end.
Definition SSB_ConfigMobility__helper1 : (forall a : SSB_ConfigMobility__Type, SSB_ConfigMobility__cond a -> SSB_ConfigMobility__list_cond (SSB_ConfigMobility__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SSB_ConfigMobility__helper2 : (forall a : SSB_ConfigMobility__Type, SSB_ConfigMobility__F2 (SSB_ConfigMobility__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SSB_ConfigMobility__helper3 : (forall b : SSB_ConfigMobility__list_type, SSB_ConfigMobility__list_cond b -> SSB_ConfigMobility__cond (SSB_ConfigMobility__F2 b) /\ SSB_ConfigMobility__F1 (SSB_ConfigMobility__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SSB_ConfigMobility__cond, SSB_ConfigMobility__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SSB_ConfigMobility__Format : T_Format SSB_ConfigMobility__Type SSB_ConfigMobility__cond :=
 proj2_format SSB_ConfigMobility__cond SSB_ConfigMobility__list_format  SSB_ConfigMobility__F1 SSB_ConfigMobility__F2 SSB_ConfigMobility__helper1 SSB_ConfigMobility__helper2 SSB_ConfigMobility__helper3.

Opaque SSB_ConfigMobility__cond SSB_ConfigMobility__Format.

