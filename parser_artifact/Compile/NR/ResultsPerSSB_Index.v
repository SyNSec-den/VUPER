Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Record ResultsPerSSB_Index__Type : Set :=
  make__ResultsPerSSB_Index__Type {
    ResultsPerSSB_Index__ssb_Index : SSB_Index__Type ;
    ResultsPerSSB_Index__ssb_Results : option MeasQuantityResults__Type ;
}.
Definition ResultsPerSSB_Index__list := (
 Nor SSB_Index__Type SSB_Index__cond ::
 Opt MeasQuantityResults__Type MeasQuantityResults__cond ::
 nil).
Definition ResultsPerSSB_Index__cond z := 
  SSB_Index__cond (ResultsPerSSB_Index__ssb_Index z) /\
  opt_cond MeasQuantityResults__cond (ResultsPerSSB_Index__ssb_Results z) /\
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

Definition ResultsPerSSB_Index__Format_Type := Eval cbn in seq_format_prod ResultsPerSSB_Index__list.
Definition ResultsPerSSB_Index__Format_list : ResultsPerSSB_Index__Format_Type :=
  (SSB_Index__Format, (MeasQuantityResults__Format, unit_format)).
Definition ResultsPerSSB_Index__list__Format := (*Eval compute in *) seq_format ResultsPerSSB_Index__list ResultsPerSSB_Index__Format_list.
Definition ResultsPerSSB_Index__F1 z :=
  (ResultsPerSSB_Index__ssb_Index z, (ResultsPerSSB_Index__ssb_Results z, tt)).
Definition ResultsPerSSB_Index__F2 (y : seq_type ResultsPerSSB_Index__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ResultsPerSSB_Index__Type i0 i1
  end.
Lemma ResultsPerSSB_Index__F1F2_cond (z : ResultsPerSSB_Index__Type)
  : ResultsPerSSB_Index__cond z ->
  (seq_cond ResultsPerSSB_Index__list (ResultsPerSSB_Index__F1 z)).
intro H. unfold ResultsPerSSB_Index__cond in H. simpl. auto. Qed.
Lemma ResultsPerSSB_Index__F1F2_cond2 (z : ResultsPerSSB_Index__Type)
 : ResultsPerSSB_Index__F2 (ResultsPerSSB_Index__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ResultsPerSSB_Index__F2F1_cond (y : seq_type ResultsPerSSB_Index__list)
  : seq_cond ResultsPerSSB_Index__list y ->
 (ResultsPerSSB_Index__cond (ResultsPerSSB_Index__F2 y)) /\  ResultsPerSSB_Index__F1 (ResultsPerSSB_Index__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ResultsPerSSB_Index__cond. simpl in *. auto.
 - simpl. unfold ResultsPerSSB_Index__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ResultsPerSSB_Index__Format : T_Format ResultsPerSSB_Index__Type ResultsPerSSB_Index__cond :=
        proj2_format  ResultsPerSSB_Index__cond ResultsPerSSB_Index__list__Format
    ResultsPerSSB_Index__F1 ResultsPerSSB_Index__F2 ResultsPerSSB_Index__F1F2_cond  ResultsPerSSB_Index__F1F2_cond2 ResultsPerSSB_Index__F2F1_cond.
Opaque ResultsPerSSB_Index__cond ResultsPerSSB_Index__Format.

