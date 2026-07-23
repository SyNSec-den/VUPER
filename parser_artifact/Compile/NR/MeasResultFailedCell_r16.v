Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Record MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Type : Set :=
  make__MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Type {
    MeasResultFailedCell_r16__measResult_r16__cellResults_r16__resultsSSB_Cell_r16 : MeasQuantityResults__Type ;
}.
Definition MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list := (
 Nor MeasQuantityResults__Type MeasQuantityResults__cond ::
 nil).
Definition MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond z := 
  MeasQuantityResults__cond (MeasResultFailedCell_r16__measResult_r16__cellResults_r16__resultsSSB_Cell_r16 z) /\
  True.

Require Import NR.ResultsPerSSB_IndexList.

Opaque ResultsPerSSB_IndexList__cond ResultsPerSSB_IndexList__Format.

Record MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type : Set :=
  make__MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type {
    MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__resultsSSB_Indexes_r16 : ResultsPerSSB_IndexList__Type ;
}.
Definition MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list := (
 Nor ResultsPerSSB_IndexList__Type ResultsPerSSB_IndexList__cond ::
 nil).
Definition MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond z := 
  ResultsPerSSB_IndexList__cond (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__resultsSSB_Indexes_r16 z) /\
  True.

Record MeasResultFailedCell_r16__measResult_r16__Type : Set :=
  make__MeasResultFailedCell_r16__measResult_r16__Type {
    MeasResultFailedCell_r16__measResult_r16__cellResults_r16 : MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Type ;
    MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16 : MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type ;
}.
Definition MeasResultFailedCell_r16__measResult_r16__list := (
 Nor MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Type MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond ::
 Nor MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond ::
 nil).
Definition MeasResultFailedCell_r16__measResult_r16__cond z := 
  MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond (MeasResultFailedCell_r16__measResult_r16__cellResults_r16 z) /\
  MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16 z) /\
  True.

Record MeasResultFailedCell_r16__Type : Set :=
  make__MeasResultFailedCell_r16__Type {
    MeasResultFailedCell_r16__cgi_Info : CGI_Info_Logging_r16__Type ;
    MeasResultFailedCell_r16__measResult_r16 : MeasResultFailedCell_r16__measResult_r16__Type ;
}.
Definition MeasResultFailedCell_r16__list := (
 Nor CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
 Nor MeasResultFailedCell_r16__measResult_r16__Type MeasResultFailedCell_r16__measResult_r16__cond ::
 nil).
Definition MeasResultFailedCell_r16__cond z := 
  CGI_Info_Logging_r16__cond (MeasResultFailedCell_r16__cgi_Info z) /\
  MeasResultFailedCell_r16__measResult_r16__cond (MeasResultFailedCell_r16__measResult_r16 z) /\
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

Definition MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Format_Type := Eval cbn in seq_format_prod MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list.
Definition MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Format_list : MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Format_Type :=
  (MeasQuantityResults__Format, unit_format).
Definition MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list__Format := (*Eval compute in *) seq_format MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Format_list.
Definition MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1 z :=
  (MeasResultFailedCell_r16__measResult_r16__cellResults_r16__resultsSSB_Cell_r16 z, tt).
Definition MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F2 (y : seq_type MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list) :=
  match y with
  | (i0, _)=>
    make__MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Type i0
  end.
Lemma MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1F2_cond (z : MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Type)
  : MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond z ->
  (seq_cond MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list (MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1 z)).
intro H. unfold MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1F2_cond2 (z : MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Type)
 : MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F2 (MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F2F1_cond (y : seq_type MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list)
  : seq_cond MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list y ->
 (MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond (MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F2 y)) /\  MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1 (MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Format : T_Format MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Type MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond :=
        proj2_format  MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond MeasResultFailedCell_r16__measResult_r16__cellResults_r16__list__Format
    MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1 MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F2 MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1F2_cond  MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F1F2_cond2 MeasResultFailedCell_r16__measResult_r16__cellResults_r16__F2F1_cond.
Opaque MeasResultFailedCell_r16__measResult_r16__cellResults_r16__cond MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Format.


Definition MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format_Type := Eval cbn in seq_format_prod MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list.
Definition MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format_list : MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format_Type :=
  (ResultsPerSSB_IndexList__Format, unit_format).
Definition MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list__Format := (*Eval compute in *) seq_format MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format_list.
Definition MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1 z :=
  (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__resultsSSB_Indexes_r16 z, tt).
Definition MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F2 (y : seq_type MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list) :=
  match y with
  | (i0, _)=>
    make__MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type i0
  end.
Lemma MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1F2_cond (z : MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type)
  : MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond z ->
  (seq_cond MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1 z)).
intro H. unfold MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1F2_cond2 (z : MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type)
 : MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F2 (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F2F1_cond (y : seq_type MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list)
  : seq_cond MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list y ->
 (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F2 y)) /\  MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1 (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format : T_Format MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Type MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond :=
        proj2_format  MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__list__Format
    MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1 MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F2 MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1F2_cond  MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F1F2_cond2 MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__F2F1_cond.
Opaque MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__cond MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format.


Definition MeasResultFailedCell_r16__measResult_r16__Format_Type := Eval cbn in seq_format_prod MeasResultFailedCell_r16__measResult_r16__list.
Definition MeasResultFailedCell_r16__measResult_r16__Format_list : MeasResultFailedCell_r16__measResult_r16__Format_Type :=
  (MeasResultFailedCell_r16__measResult_r16__cellResults_r16__Format, (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16__Format, unit_format)).
Definition MeasResultFailedCell_r16__measResult_r16__list__Format := (*Eval compute in *) seq_format MeasResultFailedCell_r16__measResult_r16__list MeasResultFailedCell_r16__measResult_r16__Format_list.
Definition MeasResultFailedCell_r16__measResult_r16__F1 z :=
  (MeasResultFailedCell_r16__measResult_r16__cellResults_r16 z, (MeasResultFailedCell_r16__measResult_r16__rsIndexResults_r16 z, tt)).
Definition MeasResultFailedCell_r16__measResult_r16__F2 (y : seq_type MeasResultFailedCell_r16__measResult_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultFailedCell_r16__measResult_r16__Type i0 i1
  end.
Lemma MeasResultFailedCell_r16__measResult_r16__F1F2_cond (z : MeasResultFailedCell_r16__measResult_r16__Type)
  : MeasResultFailedCell_r16__measResult_r16__cond z ->
  (seq_cond MeasResultFailedCell_r16__measResult_r16__list (MeasResultFailedCell_r16__measResult_r16__F1 z)).
intro H. unfold MeasResultFailedCell_r16__measResult_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultFailedCell_r16__measResult_r16__F1F2_cond2 (z : MeasResultFailedCell_r16__measResult_r16__Type)
 : MeasResultFailedCell_r16__measResult_r16__F2 (MeasResultFailedCell_r16__measResult_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultFailedCell_r16__measResult_r16__F2F1_cond (y : seq_type MeasResultFailedCell_r16__measResult_r16__list)
  : seq_cond MeasResultFailedCell_r16__measResult_r16__list y ->
 (MeasResultFailedCell_r16__measResult_r16__cond (MeasResultFailedCell_r16__measResult_r16__F2 y)) /\  MeasResultFailedCell_r16__measResult_r16__F1 (MeasResultFailedCell_r16__measResult_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultFailedCell_r16__measResult_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultFailedCell_r16__measResult_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultFailedCell_r16__measResult_r16__Format : T_Format MeasResultFailedCell_r16__measResult_r16__Type MeasResultFailedCell_r16__measResult_r16__cond :=
        proj2_format  MeasResultFailedCell_r16__measResult_r16__cond MeasResultFailedCell_r16__measResult_r16__list__Format
    MeasResultFailedCell_r16__measResult_r16__F1 MeasResultFailedCell_r16__measResult_r16__F2 MeasResultFailedCell_r16__measResult_r16__F1F2_cond  MeasResultFailedCell_r16__measResult_r16__F1F2_cond2 MeasResultFailedCell_r16__measResult_r16__F2F1_cond.
Opaque MeasResultFailedCell_r16__measResult_r16__cond MeasResultFailedCell_r16__measResult_r16__Format.


Definition MeasResultFailedCell_r16__Format_Type := Eval cbn in seq_format_prod MeasResultFailedCell_r16__list.
Definition MeasResultFailedCell_r16__Format_list : MeasResultFailedCell_r16__Format_Type :=
  (CGI_Info_Logging_r16__Format, (MeasResultFailedCell_r16__measResult_r16__Format, unit_format)).
Definition MeasResultFailedCell_r16__list__Format := (*Eval compute in *) seq_format MeasResultFailedCell_r16__list MeasResultFailedCell_r16__Format_list.
Definition MeasResultFailedCell_r16__F1 z :=
  (MeasResultFailedCell_r16__cgi_Info z, (MeasResultFailedCell_r16__measResult_r16 z, tt)).
Definition MeasResultFailedCell_r16__F2 (y : seq_type MeasResultFailedCell_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultFailedCell_r16__Type i0 i1
  end.
Lemma MeasResultFailedCell_r16__F1F2_cond (z : MeasResultFailedCell_r16__Type)
  : MeasResultFailedCell_r16__cond z ->
  (seq_cond MeasResultFailedCell_r16__list (MeasResultFailedCell_r16__F1 z)).
intro H. unfold MeasResultFailedCell_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultFailedCell_r16__F1F2_cond2 (z : MeasResultFailedCell_r16__Type)
 : MeasResultFailedCell_r16__F2 (MeasResultFailedCell_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultFailedCell_r16__F2F1_cond (y : seq_type MeasResultFailedCell_r16__list)
  : seq_cond MeasResultFailedCell_r16__list y ->
 (MeasResultFailedCell_r16__cond (MeasResultFailedCell_r16__F2 y)) /\  MeasResultFailedCell_r16__F1 (MeasResultFailedCell_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultFailedCell_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultFailedCell_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultFailedCell_r16__Format : T_Format MeasResultFailedCell_r16__Type MeasResultFailedCell_r16__cond :=
        proj2_format  MeasResultFailedCell_r16__cond MeasResultFailedCell_r16__list__Format
    MeasResultFailedCell_r16__F1 MeasResultFailedCell_r16__F2 MeasResultFailedCell_r16__F1F2_cond  MeasResultFailedCell_r16__F1F2_cond2 MeasResultFailedCell_r16__F2F1_cond.
Opaque MeasResultFailedCell_r16__cond MeasResultFailedCell_r16__Format.

