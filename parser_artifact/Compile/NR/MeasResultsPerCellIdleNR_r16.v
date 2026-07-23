Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRQ_Range.

Opaque RSRQ_Range__cond RSRQ_Range__Format.

Require Import NR.ResultsPerSSB_IndexList_r16.

Opaque ResultsPerSSB_IndexList_r16__cond ResultsPerSSB_IndexList_r16__Format.

Record MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type : Set :=
  make__MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type {
    MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__rsrp_Result_r16 : option RSRP_Range__Type ;
    MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__rsrq_Result_r16 : option RSRQ_Range__Type ;
    MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__resultsSSB_Indexes_r16 : option ResultsPerSSB_IndexList_r16__Type ;
}.
Definition MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list := (
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt RSRQ_Range__Type RSRQ_Range__cond ::
 Opt ResultsPerSSB_IndexList_r16__Type ResultsPerSSB_IndexList_r16__cond ::
 nil).
Definition MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond z := 
  opt_cond RSRP_Range__cond (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__rsrp_Result_r16 z) /\
  opt_cond RSRQ_Range__cond (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__rsrq_Result_r16 z) /\
  opt_cond ResultsPerSSB_IndexList_r16__cond (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__resultsSSB_Indexes_r16 z) /\
  True.

Record MeasResultsPerCellIdleNR_r16__Type : Set :=
  make__MeasResultsPerCellIdleNR_r16__Type {
    MeasResultsPerCellIdleNR_r16__physCellId_r16 : PhysCellId__Type ;
    MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16 : MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type ;
}.
Definition MeasResultsPerCellIdleNR_r16__root_list : list seq_elem := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond ::
 nil).
Definition MeasResultsPerCellIdleNR_r16__ext_list : list typ := (
  nil).
Definition MeasResultsPerCellIdleNR_r16__cond (z : MeasResultsPerCellIdleNR_r16__Type) := 
(  PhysCellId__cond (MeasResultsPerCellIdleNR_r16__physCellId_r16 z) /\
  MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16 z) /\
  True) /\ 
(  True).


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

Definition MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format_Type := Eval cbn in seq_format_prod MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list.
Definition MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format_list : MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format_Type :=
  (RSRP_Range__Format, (RSRQ_Range__Format, (ResultsPerSSB_IndexList_r16__Format, unit_format))).
Definition MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list__Format := (*Eval compute in *) seq_format MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format_list.
Definition MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1 z :=
  (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__rsrp_Result_r16 z, (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__rsrq_Result_r16 z, (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__resultsSSB_Indexes_r16 z, tt))).
Definition MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F2 (y : seq_type MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type i0 i1 i2
  end.
Lemma MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1F2_cond (z : MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type)
  : MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond z ->
  (seq_cond MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1 z)).
intro H. unfold MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1F2_cond2 (z : MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type)
 : MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F2 (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F2F1_cond (y : seq_type MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list)
  : seq_cond MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list y ->
 (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F2 y)) /\  MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1 (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format : T_Format MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Type MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond :=
        proj2_format  MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__list__Format
    MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1 MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F2 MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1F2_cond  MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F1F2_cond2 MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__F2F1_cond.
Opaque MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__cond MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format.


Definition MeasResultsPerCellIdleNR_r16__root_Format_Type := Eval cbn in seq_format_prod MeasResultsPerCellIdleNR_r16__root_list.
Definition MeasResultsPerCellIdleNR_r16__root_Format_list : MeasResultsPerCellIdleNR_r16__root_Format_Type :=
  (PhysCellId__Format, (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16__Format, unit_format)).

Definition MeasResultsPerCellIdleNR_r16__ext_Format_Type := Eval cbn in get_formats MeasResultsPerCellIdleNR_r16__ext_list.
Definition MeasResultsPerCellIdleNR_r16__ext_Format_list : MeasResultsPerCellIdleNR_r16__ext_Format_Type :=
  unit__Format.

Definition MeasResultsPerCellIdleNR_r16__list_type : Set := (seq_type MeasResultsPerCellIdleNR_r16__root_list) * (seq_ext_type MeasResultsPerCellIdleNR_r16__ext_list).
Definition MeasResultsPerCellIdleNR_r16__list_cond (z : MeasResultsPerCellIdleNR_r16__list_type) : Prop :=
        (seq_cond MeasResultsPerCellIdleNR_r16__root_list (fst z)) /\ (seq_ext_cond MeasResultsPerCellIdleNR_r16__ext_list (snd z)).
Definition MeasResultsPerCellIdleNR_r16__list_format : T_Format MeasResultsPerCellIdleNR_r16__list_type MeasResultsPerCellIdleNR_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultsPerCellIdleNR_r16__root_list MeasResultsPerCellIdleNR_r16__root_Format_list MeasResultsPerCellIdleNR_r16__ext_list MeasResultsPerCellIdleNR_r16__ext_Format_list.

Opaque MeasResultsPerCellIdleNR_r16__list_format.
Definition MeasResultsPerCellIdleNR_r16__F1 (z : MeasResultsPerCellIdleNR_r16__Type) : MeasResultsPerCellIdleNR_r16__list_type :=
  (((MeasResultsPerCellIdleNR_r16__physCellId_r16 z, (MeasResultsPerCellIdleNR_r16__measIdleResultNR_r16 z, tt))), (
tt)).
Definition MeasResultsPerCellIdleNR_r16__F2 (y : MeasResultsPerCellIdleNR_r16__list_type) : MeasResultsPerCellIdleNR_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__MeasResultsPerCellIdleNR_r16__Type j0 j1
  end.
Definition MeasResultsPerCellIdleNR_r16__helper1 : (forall a : MeasResultsPerCellIdleNR_r16__Type, MeasResultsPerCellIdleNR_r16__cond a -> MeasResultsPerCellIdleNR_r16__list_cond (MeasResultsPerCellIdleNR_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultsPerCellIdleNR_r16__helper2 : (forall a : MeasResultsPerCellIdleNR_r16__Type, MeasResultsPerCellIdleNR_r16__F2 (MeasResultsPerCellIdleNR_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultsPerCellIdleNR_r16__helper3 : (forall b : MeasResultsPerCellIdleNR_r16__list_type, MeasResultsPerCellIdleNR_r16__list_cond b -> MeasResultsPerCellIdleNR_r16__cond (MeasResultsPerCellIdleNR_r16__F2 b) /\ MeasResultsPerCellIdleNR_r16__F1 (MeasResultsPerCellIdleNR_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultsPerCellIdleNR_r16__cond, MeasResultsPerCellIdleNR_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultsPerCellIdleNR_r16__Format : T_Format MeasResultsPerCellIdleNR_r16__Type MeasResultsPerCellIdleNR_r16__cond :=
 proj2_format MeasResultsPerCellIdleNR_r16__cond MeasResultsPerCellIdleNR_r16__list_format  MeasResultsPerCellIdleNR_r16__F1 MeasResultsPerCellIdleNR_r16__F2 MeasResultsPerCellIdleNR_r16__helper1 MeasResultsPerCellIdleNR_r16__helper2 MeasResultsPerCellIdleNR_r16__helper3.

Opaque MeasResultsPerCellIdleNR_r16__cond MeasResultsPerCellIdleNR_r16__Format.

