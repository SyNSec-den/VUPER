Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Record MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Type : Set :=
  make__MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Type {
    MeasResultRLFNR_r16__measResult_r16__cellResults_r16__resultsSSB_Cell_r16 : option MeasQuantityResults__Type ;
    MeasResultRLFNR_r16__measResult_r16__cellResults_r16__resultsCSI_RS_Cell_r16 : option MeasQuantityResults__Type ;
}.
Definition MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list := (
 Opt MeasQuantityResults__Type MeasQuantityResults__cond ::
 Opt MeasQuantityResults__Type MeasQuantityResults__cond ::
 nil).
Definition MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond z := 
  opt_cond MeasQuantityResults__cond (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__resultsSSB_Cell_r16 z) /\
  opt_cond MeasQuantityResults__cond (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__resultsCSI_RS_Cell_r16 z) /\
  True.

Require Import NR.ResultsPerSSB_IndexList.

Opaque ResultsPerSSB_IndexList__cond ResultsPerSSB_IndexList__Format.

Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Type := bit_string_fixed.
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 64 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.ResultsPerCSI_RS_IndexList.

Opaque ResultsPerCSI_RS_IndexList__cond ResultsPerCSI_RS_IndexList__Format.

Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Type := bit_string_fixed.
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 96 /\ bit_string_len_prop (fst z) (snd z)).
Record MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type : Set :=
  make__MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type {
    MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__resultsSSB_Indexes_r16 : option ResultsPerSSB_IndexList__Type ;
    MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16 : option MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Type ;
    MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__resultsCSI_RS_Indexes_r16 : option ResultsPerCSI_RS_IndexList__Type ;
    MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16 : option MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Type ;
}.
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list := (
 Opt ResultsPerSSB_IndexList__Type ResultsPerSSB_IndexList__cond ::
 Opt MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Type MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__cond ::
 Opt ResultsPerCSI_RS_IndexList__Type ResultsPerCSI_RS_IndexList__cond ::
 Opt MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Type MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__cond ::
 nil).
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond z := 
  opt_cond ResultsPerSSB_IndexList__cond (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__resultsSSB_Indexes_r16 z) /\
  opt_cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__cond (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16 z) /\
  opt_cond ResultsPerCSI_RS_IndexList__cond (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__resultsCSI_RS_Indexes_r16 z) /\
  opt_cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__cond (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16 z) /\
  True.

Record MeasResultRLFNR_r16__measResult_r16__Type : Set :=
  make__MeasResultRLFNR_r16__measResult_r16__Type {
    MeasResultRLFNR_r16__measResult_r16__cellResults_r16 : MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Type ;
    MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16 : option MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type ;
}.
Definition MeasResultRLFNR_r16__measResult_r16__list := (
 Nor MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Type MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond ::
 Opt MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond ::
 nil).
Definition MeasResultRLFNR_r16__measResult_r16__cond z := 
  MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond (MeasResultRLFNR_r16__measResult_r16__cellResults_r16 z) /\
  opt_cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16 z) /\
  True.

Record MeasResultRLFNR_r16__Type : Set :=
  make__MeasResultRLFNR_r16__Type {
    MeasResultRLFNR_r16__measResult_r16 : MeasResultRLFNR_r16__measResult_r16__Type ;
}.
Definition MeasResultRLFNR_r16__list := (
 Nor MeasResultRLFNR_r16__measResult_r16__Type MeasResultRLFNR_r16__measResult_r16__cond ::
 nil).
Definition MeasResultRLFNR_r16__cond z := 
  MeasResultRLFNR_r16__measResult_r16__cond (MeasResultRLFNR_r16__measResult_r16 z) /\
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

Definition MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Format_Type := Eval cbn in seq_format_prod MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list.
Definition MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Format_list : MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Format_Type :=
  (MeasQuantityResults__Format, (MeasQuantityResults__Format, unit_format)).
Definition MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list__Format := (*Eval compute in *) seq_format MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Format_list.
Definition MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1 z :=
  (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__resultsSSB_Cell_r16 z, (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__resultsCSI_RS_Cell_r16 z, tt)).
Definition MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F2 (y : seq_type MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Type i0 i1
  end.
Lemma MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1F2_cond (z : MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Type)
  : MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond z ->
  (seq_cond MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1 z)).
intro H. unfold MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1F2_cond2 (z : MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Type)
 : MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F2 (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F2F1_cond (y : seq_type MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list)
  : seq_cond MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list y ->
 (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F2 y)) /\  MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1 (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Format : T_Format MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Type MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond :=
        proj2_format  MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond MeasResultRLFNR_r16__measResult_r16__cellResults_r16__list__Format
    MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1 MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F2 MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1F2_cond  MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F1F2_cond2 MeasResultRLFNR_r16__measResult_r16__cellResults_r16__F2F1_cond.
Opaque MeasResultRLFNR_r16__measResult_r16__cellResults_r16__cond MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Format.

Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Format : T_Format MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Type MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__cond := (* Eval compute in *) bit_string_fixed_format 64.
Opaque MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Format.

Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Format : T_Format MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Type MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__cond := (* Eval compute in *) bit_string_fixed_format 96.
Opaque MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Format.


Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format_Type := Eval cbn in seq_format_prod MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list.
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format_list : MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format_Type :=
  (ResultsPerSSB_IndexList__Format, (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16__Format, (ResultsPerCSI_RS_IndexList__Format, (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16__Format, unit_format)))).
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list__Format := (*Eval compute in *) seq_format MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format_list.
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1 z :=
  (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__resultsSSB_Indexes_r16 z, (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__ssbRLMConfigBitmap_r16 z, (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__resultsCSI_RS_Indexes_r16 z, (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__csi_rsRLMConfigBitmap_r16 z, tt)))).
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F2 (y : seq_type MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type i0 i1 i2 i3
  end.
Lemma MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1F2_cond (z : MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type)
  : MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond z ->
  (seq_cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1 z)).
intro H. unfold MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1F2_cond2 (z : MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type)
 : MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F2 (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F2F1_cond (y : seq_type MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list)
  : seq_cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list y ->
 (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F2 y)) /\  MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1 (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format : T_Format MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Type MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond :=
        proj2_format  MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__list__Format
    MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1 MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F2 MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1F2_cond  MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F1F2_cond2 MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__F2F1_cond.
Opaque MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__cond MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format.


Definition MeasResultRLFNR_r16__measResult_r16__Format_Type := Eval cbn in seq_format_prod MeasResultRLFNR_r16__measResult_r16__list.
Definition MeasResultRLFNR_r16__measResult_r16__Format_list : MeasResultRLFNR_r16__measResult_r16__Format_Type :=
  (MeasResultRLFNR_r16__measResult_r16__cellResults_r16__Format, (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16__Format, unit_format)).
Definition MeasResultRLFNR_r16__measResult_r16__list__Format := (*Eval compute in *) seq_format MeasResultRLFNR_r16__measResult_r16__list MeasResultRLFNR_r16__measResult_r16__Format_list.
Definition MeasResultRLFNR_r16__measResult_r16__F1 z :=
  (MeasResultRLFNR_r16__measResult_r16__cellResults_r16 z, (MeasResultRLFNR_r16__measResult_r16__rsIndexResults_r16 z, tt)).
Definition MeasResultRLFNR_r16__measResult_r16__F2 (y : seq_type MeasResultRLFNR_r16__measResult_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultRLFNR_r16__measResult_r16__Type i0 i1
  end.
Lemma MeasResultRLFNR_r16__measResult_r16__F1F2_cond (z : MeasResultRLFNR_r16__measResult_r16__Type)
  : MeasResultRLFNR_r16__measResult_r16__cond z ->
  (seq_cond MeasResultRLFNR_r16__measResult_r16__list (MeasResultRLFNR_r16__measResult_r16__F1 z)).
intro H. unfold MeasResultRLFNR_r16__measResult_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultRLFNR_r16__measResult_r16__F1F2_cond2 (z : MeasResultRLFNR_r16__measResult_r16__Type)
 : MeasResultRLFNR_r16__measResult_r16__F2 (MeasResultRLFNR_r16__measResult_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultRLFNR_r16__measResult_r16__F2F1_cond (y : seq_type MeasResultRLFNR_r16__measResult_r16__list)
  : seq_cond MeasResultRLFNR_r16__measResult_r16__list y ->
 (MeasResultRLFNR_r16__measResult_r16__cond (MeasResultRLFNR_r16__measResult_r16__F2 y)) /\  MeasResultRLFNR_r16__measResult_r16__F1 (MeasResultRLFNR_r16__measResult_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultRLFNR_r16__measResult_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultRLFNR_r16__measResult_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultRLFNR_r16__measResult_r16__Format : T_Format MeasResultRLFNR_r16__measResult_r16__Type MeasResultRLFNR_r16__measResult_r16__cond :=
        proj2_format  MeasResultRLFNR_r16__measResult_r16__cond MeasResultRLFNR_r16__measResult_r16__list__Format
    MeasResultRLFNR_r16__measResult_r16__F1 MeasResultRLFNR_r16__measResult_r16__F2 MeasResultRLFNR_r16__measResult_r16__F1F2_cond  MeasResultRLFNR_r16__measResult_r16__F1F2_cond2 MeasResultRLFNR_r16__measResult_r16__F2F1_cond.
Opaque MeasResultRLFNR_r16__measResult_r16__cond MeasResultRLFNR_r16__measResult_r16__Format.


Definition MeasResultRLFNR_r16__Format_Type := Eval cbn in seq_format_prod MeasResultRLFNR_r16__list.
Definition MeasResultRLFNR_r16__Format_list : MeasResultRLFNR_r16__Format_Type :=
  (MeasResultRLFNR_r16__measResult_r16__Format, unit_format).
Definition MeasResultRLFNR_r16__list__Format := (*Eval compute in *) seq_format MeasResultRLFNR_r16__list MeasResultRLFNR_r16__Format_list.
Definition MeasResultRLFNR_r16__F1 z :=
  (MeasResultRLFNR_r16__measResult_r16 z, tt).
Definition MeasResultRLFNR_r16__F2 (y : seq_type MeasResultRLFNR_r16__list) :=
  match y with
  | (i0, _)=>
    make__MeasResultRLFNR_r16__Type i0
  end.
Lemma MeasResultRLFNR_r16__F1F2_cond (z : MeasResultRLFNR_r16__Type)
  : MeasResultRLFNR_r16__cond z ->
  (seq_cond MeasResultRLFNR_r16__list (MeasResultRLFNR_r16__F1 z)).
intro H. unfold MeasResultRLFNR_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultRLFNR_r16__F1F2_cond2 (z : MeasResultRLFNR_r16__Type)
 : MeasResultRLFNR_r16__F2 (MeasResultRLFNR_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultRLFNR_r16__F2F1_cond (y : seq_type MeasResultRLFNR_r16__list)
  : seq_cond MeasResultRLFNR_r16__list y ->
 (MeasResultRLFNR_r16__cond (MeasResultRLFNR_r16__F2 y)) /\  MeasResultRLFNR_r16__F1 (MeasResultRLFNR_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultRLFNR_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultRLFNR_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultRLFNR_r16__Format : T_Format MeasResultRLFNR_r16__Type MeasResultRLFNR_r16__cond :=
        proj2_format  MeasResultRLFNR_r16__cond MeasResultRLFNR_r16__list__Format
    MeasResultRLFNR_r16__F1 MeasResultRLFNR_r16__F2 MeasResultRLFNR_r16__F1F2_cond  MeasResultRLFNR_r16__F1F2_cond2 MeasResultRLFNR_r16__F2F1_cond.
Opaque MeasResultRLFNR_r16__cond MeasResultRLFNR_r16__Format.

