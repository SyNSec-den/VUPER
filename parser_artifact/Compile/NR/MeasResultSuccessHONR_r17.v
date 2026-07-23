Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Record MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type : Set :=
  make__MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type {
    MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__resultsSSB_Cell_r17 : option MeasQuantityResults__Type ;
    MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__resultsCSI_RS_Cell_r17 : option MeasQuantityResults__Type ;
}.
Definition MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list := (
 Opt MeasQuantityResults__Type MeasQuantityResults__cond ::
 Opt MeasQuantityResults__Type MeasQuantityResults__cond ::
 nil).
Definition MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond z := 
  opt_cond MeasQuantityResults__cond (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__resultsSSB_Cell_r17 z) /\
  opt_cond MeasQuantityResults__cond (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__resultsCSI_RS_Cell_r17 z) /\
  True.

Require Import NR.ResultsPerSSB_IndexList.

Opaque ResultsPerSSB_IndexList__cond ResultsPerSSB_IndexList__Format.

Require Import NR.ResultsPerCSI_RS_IndexList.

Opaque ResultsPerCSI_RS_IndexList__cond ResultsPerCSI_RS_IndexList__Format.

Record MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type : Set :=
  make__MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type {
    MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__resultsSSB_Indexes_r17 : option ResultsPerSSB_IndexList__Type ;
    MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__resultsCSI_RS_Indexes_r17 : option ResultsPerCSI_RS_IndexList__Type ;
}.
Definition MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list := (
 Opt ResultsPerSSB_IndexList__Type ResultsPerSSB_IndexList__cond ::
 Opt ResultsPerCSI_RS_IndexList__Type ResultsPerCSI_RS_IndexList__cond ::
 nil).
Definition MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond z := 
  opt_cond ResultsPerSSB_IndexList__cond (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__resultsSSB_Indexes_r17 z) /\
  opt_cond ResultsPerCSI_RS_IndexList__cond (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__resultsCSI_RS_Indexes_r17 z) /\
  True.

Record MeasResultSuccessHONR_r17__measResult_r17__Type : Set :=
  make__MeasResultSuccessHONR_r17__measResult_r17__Type {
    MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17 : MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type ;
    MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17 : MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type ;
}.
Definition MeasResultSuccessHONR_r17__measResult_r17__list := (
 Nor MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond ::
 Nor MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond ::
 nil).
Definition MeasResultSuccessHONR_r17__measResult_r17__cond z := 
  MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17 z) /\
  MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17 z) /\
  True.

Record MeasResultSuccessHONR_r17__Type : Set :=
  make__MeasResultSuccessHONR_r17__Type {
    MeasResultSuccessHONR_r17__measResult_r17 : MeasResultSuccessHONR_r17__measResult_r17__Type ;
}.
Definition MeasResultSuccessHONR_r17__list := (
 Nor MeasResultSuccessHONR_r17__measResult_r17__Type MeasResultSuccessHONR_r17__measResult_r17__cond ::
 nil).
Definition MeasResultSuccessHONR_r17__cond z := 
  MeasResultSuccessHONR_r17__measResult_r17__cond (MeasResultSuccessHONR_r17__measResult_r17 z) /\
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

Definition MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format_Type := Eval cbn in seq_format_prod MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list.
Definition MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format_list : MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format_Type :=
  (MeasQuantityResults__Format, (MeasQuantityResults__Format, unit_format)).
Definition MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list__Format := (*Eval compute in *) seq_format MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format_list.
Definition MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1 z :=
  (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__resultsSSB_Cell_r17 z, (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__resultsCSI_RS_Cell_r17 z, tt)).
Definition MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F2 (y : seq_type MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type i0 i1
  end.
Lemma MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1F2_cond (z : MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type)
  : MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond z ->
  (seq_cond MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1 z)).
intro H. unfold MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond in H. simpl. auto. Qed.
Lemma MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1F2_cond2 (z : MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type)
 : MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F2 (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F2F1_cond (y : seq_type MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list)
  : seq_cond MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list y ->
 (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F2 y)) /\  MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1 (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond. simpl in *. auto.
 - simpl. unfold MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format : T_Format MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Type MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond :=
        proj2_format  MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__list__Format
    MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1 MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F2 MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1F2_cond  MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F1F2_cond2 MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__F2F1_cond.
Opaque MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__cond MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format.


Definition MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format_Type := Eval cbn in seq_format_prod MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list.
Definition MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format_list : MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format_Type :=
  (ResultsPerSSB_IndexList__Format, (ResultsPerCSI_RS_IndexList__Format, unit_format)).
Definition MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list__Format := (*Eval compute in *) seq_format MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format_list.
Definition MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1 z :=
  (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__resultsSSB_Indexes_r17 z, (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__resultsCSI_RS_Indexes_r17 z, tt)).
Definition MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F2 (y : seq_type MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type i0 i1
  end.
Lemma MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1F2_cond (z : MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type)
  : MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond z ->
  (seq_cond MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1 z)).
intro H. unfold MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond in H. simpl. auto. Qed.
Lemma MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1F2_cond2 (z : MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type)
 : MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F2 (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F2F1_cond (y : seq_type MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list)
  : seq_cond MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list y ->
 (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F2 y)) /\  MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1 (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond. simpl in *. auto.
 - simpl. unfold MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format : T_Format MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Type MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond :=
        proj2_format  MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__list__Format
    MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1 MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F2 MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1F2_cond  MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F1F2_cond2 MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__F2F1_cond.
Opaque MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__cond MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format.


Definition MeasResultSuccessHONR_r17__measResult_r17__Format_Type := Eval cbn in seq_format_prod MeasResultSuccessHONR_r17__measResult_r17__list.
Definition MeasResultSuccessHONR_r17__measResult_r17__Format_list : MeasResultSuccessHONR_r17__measResult_r17__Format_Type :=
  (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17__Format, (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17__Format, unit_format)).
Definition MeasResultSuccessHONR_r17__measResult_r17__list__Format := (*Eval compute in *) seq_format MeasResultSuccessHONR_r17__measResult_r17__list MeasResultSuccessHONR_r17__measResult_r17__Format_list.
Definition MeasResultSuccessHONR_r17__measResult_r17__F1 z :=
  (MeasResultSuccessHONR_r17__measResult_r17__cellResults_r17 z, (MeasResultSuccessHONR_r17__measResult_r17__rsIndexResults_r17 z, tt)).
Definition MeasResultSuccessHONR_r17__measResult_r17__F2 (y : seq_type MeasResultSuccessHONR_r17__measResult_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultSuccessHONR_r17__measResult_r17__Type i0 i1
  end.
Lemma MeasResultSuccessHONR_r17__measResult_r17__F1F2_cond (z : MeasResultSuccessHONR_r17__measResult_r17__Type)
  : MeasResultSuccessHONR_r17__measResult_r17__cond z ->
  (seq_cond MeasResultSuccessHONR_r17__measResult_r17__list (MeasResultSuccessHONR_r17__measResult_r17__F1 z)).
intro H. unfold MeasResultSuccessHONR_r17__measResult_r17__cond in H. simpl. auto. Qed.
Lemma MeasResultSuccessHONR_r17__measResult_r17__F1F2_cond2 (z : MeasResultSuccessHONR_r17__measResult_r17__Type)
 : MeasResultSuccessHONR_r17__measResult_r17__F2 (MeasResultSuccessHONR_r17__measResult_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultSuccessHONR_r17__measResult_r17__F2F1_cond (y : seq_type MeasResultSuccessHONR_r17__measResult_r17__list)
  : seq_cond MeasResultSuccessHONR_r17__measResult_r17__list y ->
 (MeasResultSuccessHONR_r17__measResult_r17__cond (MeasResultSuccessHONR_r17__measResult_r17__F2 y)) /\  MeasResultSuccessHONR_r17__measResult_r17__F1 (MeasResultSuccessHONR_r17__measResult_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultSuccessHONR_r17__measResult_r17__cond. simpl in *. auto.
 - simpl. unfold MeasResultSuccessHONR_r17__measResult_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultSuccessHONR_r17__measResult_r17__Format : T_Format MeasResultSuccessHONR_r17__measResult_r17__Type MeasResultSuccessHONR_r17__measResult_r17__cond :=
        proj2_format  MeasResultSuccessHONR_r17__measResult_r17__cond MeasResultSuccessHONR_r17__measResult_r17__list__Format
    MeasResultSuccessHONR_r17__measResult_r17__F1 MeasResultSuccessHONR_r17__measResult_r17__F2 MeasResultSuccessHONR_r17__measResult_r17__F1F2_cond  MeasResultSuccessHONR_r17__measResult_r17__F1F2_cond2 MeasResultSuccessHONR_r17__measResult_r17__F2F1_cond.
Opaque MeasResultSuccessHONR_r17__measResult_r17__cond MeasResultSuccessHONR_r17__measResult_r17__Format.


Definition MeasResultSuccessHONR_r17__Format_Type := Eval cbn in seq_format_prod MeasResultSuccessHONR_r17__list.
Definition MeasResultSuccessHONR_r17__Format_list : MeasResultSuccessHONR_r17__Format_Type :=
  (MeasResultSuccessHONR_r17__measResult_r17__Format, unit_format).
Definition MeasResultSuccessHONR_r17__list__Format := (*Eval compute in *) seq_format MeasResultSuccessHONR_r17__list MeasResultSuccessHONR_r17__Format_list.
Definition MeasResultSuccessHONR_r17__F1 z :=
  (MeasResultSuccessHONR_r17__measResult_r17 z, tt).
Definition MeasResultSuccessHONR_r17__F2 (y : seq_type MeasResultSuccessHONR_r17__list) :=
  match y with
  | (i0, _)=>
    make__MeasResultSuccessHONR_r17__Type i0
  end.
Lemma MeasResultSuccessHONR_r17__F1F2_cond (z : MeasResultSuccessHONR_r17__Type)
  : MeasResultSuccessHONR_r17__cond z ->
  (seq_cond MeasResultSuccessHONR_r17__list (MeasResultSuccessHONR_r17__F1 z)).
intro H. unfold MeasResultSuccessHONR_r17__cond in H. simpl. auto. Qed.
Lemma MeasResultSuccessHONR_r17__F1F2_cond2 (z : MeasResultSuccessHONR_r17__Type)
 : MeasResultSuccessHONR_r17__F2 (MeasResultSuccessHONR_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultSuccessHONR_r17__F2F1_cond (y : seq_type MeasResultSuccessHONR_r17__list)
  : seq_cond MeasResultSuccessHONR_r17__list y ->
 (MeasResultSuccessHONR_r17__cond (MeasResultSuccessHONR_r17__F2 y)) /\  MeasResultSuccessHONR_r17__F1 (MeasResultSuccessHONR_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultSuccessHONR_r17__cond. simpl in *. auto.
 - simpl. unfold MeasResultSuccessHONR_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultSuccessHONR_r17__Format : T_Format MeasResultSuccessHONR_r17__Type MeasResultSuccessHONR_r17__cond :=
        proj2_format  MeasResultSuccessHONR_r17__cond MeasResultSuccessHONR_r17__list__Format
    MeasResultSuccessHONR_r17__F1 MeasResultSuccessHONR_r17__F2 MeasResultSuccessHONR_r17__F1F2_cond  MeasResultSuccessHONR_r17__F1F2_cond2 MeasResultSuccessHONR_r17__F2F1_cond.
Opaque MeasResultSuccessHONR_r17__cond MeasResultSuccessHONR_r17__Format.

