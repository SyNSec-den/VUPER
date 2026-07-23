Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRQ_Range.

Opaque RSRQ_Range__cond RSRQ_Range__Format.

Record ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type : Set :=
  make__ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type {
    ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__ssb_RSRP_Result_r16 : option RSRP_Range__Type ;
    ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__ssb_RSRQ_Result_r16 : option RSRQ_Range__Type ;
}.
Definition ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list := (
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt RSRQ_Range__Type RSRQ_Range__cond ::
 nil).
Definition ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond z := 
  opt_cond RSRP_Range__cond (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__ssb_RSRP_Result_r16 z) /\
  opt_cond RSRQ_Range__cond (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__ssb_RSRQ_Result_r16 z) /\
  True.

Record ResultsPerSSB_IndexIdle_r16__Type : Set :=
  make__ResultsPerSSB_IndexIdle_r16__Type {
    ResultsPerSSB_IndexIdle_r16__ssb_Index_r16 : SSB_Index__Type ;
    ResultsPerSSB_IndexIdle_r16__ssb_Results_r16 : option ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type ;
}.
Definition ResultsPerSSB_IndexIdle_r16__list := (
 Nor SSB_Index__Type SSB_Index__cond ::
 Opt ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond ::
 nil).
Definition ResultsPerSSB_IndexIdle_r16__cond z := 
  SSB_Index__cond (ResultsPerSSB_IndexIdle_r16__ssb_Index_r16 z) /\
  opt_cond ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16 z) /\
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

Definition ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format_Type := Eval cbn in seq_format_prod ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list.
Definition ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format_list : ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format_Type :=
  (RSRP_Range__Format, (RSRQ_Range__Format, unit_format)).
Definition ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list__Format := (*Eval compute in *) seq_format ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format_list.
Definition ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1 z :=
  (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__ssb_RSRP_Result_r16 z, (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__ssb_RSRQ_Result_r16 z, tt)).
Definition ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F2 (y : seq_type ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type i0 i1
  end.
Lemma ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1F2_cond (z : ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type)
  : ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond z ->
  (seq_cond ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1 z)).
intro H. unfold ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond in H. simpl. auto. Qed.
Lemma ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1F2_cond2 (z : ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type)
 : ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F2 (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F2F1_cond (y : seq_type ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list)
  : seq_cond ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list y ->
 (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F2 y)) /\  ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1 (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond. simpl in *. auto.
 - simpl. unfold ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format : T_Format ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Type ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond :=
        proj2_format  ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__list__Format
    ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1 ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F2 ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1F2_cond  ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F1F2_cond2 ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__F2F1_cond.
Opaque ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__cond ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format.


Definition ResultsPerSSB_IndexIdle_r16__Format_Type := Eval cbn in seq_format_prod ResultsPerSSB_IndexIdle_r16__list.
Definition ResultsPerSSB_IndexIdle_r16__Format_list : ResultsPerSSB_IndexIdle_r16__Format_Type :=
  (SSB_Index__Format, (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16__Format, unit_format)).
Definition ResultsPerSSB_IndexIdle_r16__list__Format := (*Eval compute in *) seq_format ResultsPerSSB_IndexIdle_r16__list ResultsPerSSB_IndexIdle_r16__Format_list.
Definition ResultsPerSSB_IndexIdle_r16__F1 z :=
  (ResultsPerSSB_IndexIdle_r16__ssb_Index_r16 z, (ResultsPerSSB_IndexIdle_r16__ssb_Results_r16 z, tt)).
Definition ResultsPerSSB_IndexIdle_r16__F2 (y : seq_type ResultsPerSSB_IndexIdle_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ResultsPerSSB_IndexIdle_r16__Type i0 i1
  end.
Lemma ResultsPerSSB_IndexIdle_r16__F1F2_cond (z : ResultsPerSSB_IndexIdle_r16__Type)
  : ResultsPerSSB_IndexIdle_r16__cond z ->
  (seq_cond ResultsPerSSB_IndexIdle_r16__list (ResultsPerSSB_IndexIdle_r16__F1 z)).
intro H. unfold ResultsPerSSB_IndexIdle_r16__cond in H. simpl. auto. Qed.
Lemma ResultsPerSSB_IndexIdle_r16__F1F2_cond2 (z : ResultsPerSSB_IndexIdle_r16__Type)
 : ResultsPerSSB_IndexIdle_r16__F2 (ResultsPerSSB_IndexIdle_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ResultsPerSSB_IndexIdle_r16__F2F1_cond (y : seq_type ResultsPerSSB_IndexIdle_r16__list)
  : seq_cond ResultsPerSSB_IndexIdle_r16__list y ->
 (ResultsPerSSB_IndexIdle_r16__cond (ResultsPerSSB_IndexIdle_r16__F2 y)) /\  ResultsPerSSB_IndexIdle_r16__F1 (ResultsPerSSB_IndexIdle_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ResultsPerSSB_IndexIdle_r16__cond. simpl in *. auto.
 - simpl. unfold ResultsPerSSB_IndexIdle_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ResultsPerSSB_IndexIdle_r16__Format : T_Format ResultsPerSSB_IndexIdle_r16__Type ResultsPerSSB_IndexIdle_r16__cond :=
        proj2_format  ResultsPerSSB_IndexIdle_r16__cond ResultsPerSSB_IndexIdle_r16__list__Format
    ResultsPerSSB_IndexIdle_r16__F1 ResultsPerSSB_IndexIdle_r16__F2 ResultsPerSSB_IndexIdle_r16__F1F2_cond  ResultsPerSSB_IndexIdle_r16__F1F2_cond2 ResultsPerSSB_IndexIdle_r16__F2F1_cond.
Opaque ResultsPerSSB_IndexIdle_r16__cond ResultsPerSSB_IndexIdle_r16__Format.

