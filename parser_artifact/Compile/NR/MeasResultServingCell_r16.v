Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Lemma MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__helper1 : (1 <= maxNrofSSBs_r16)%Z. unfold maxNrofSSBs_r16.
 lia. Qed.
Lemma MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__helper2 : to_bit_sz (Z.to_nat (maxNrofSSBs_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSSBs_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__Type := Z.
Definition MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__cond := (fun z => (1 <= z <= maxNrofSSBs_r16)%Z).
Record MeasResultServingCell_r16__resultsSSB__Type : Set :=
  make__MeasResultServingCell_r16__resultsSSB__Type {
    MeasResultServingCell_r16__resultsSSB__best_ssb_Index : SSB_Index__Type ;
    MeasResultServingCell_r16__resultsSSB__best_ssb_Results : MeasQuantityResults__Type ;
    MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB : Z ;
}.
Definition MeasResultServingCell_r16__resultsSSB__list := (
 Nor SSB_Index__Type SSB_Index__cond ::
 Nor MeasQuantityResults__Type MeasQuantityResults__cond ::
 Nor Z MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__cond ::
 nil).
Definition MeasResultServingCell_r16__resultsSSB__cond z := 
  SSB_Index__cond (MeasResultServingCell_r16__resultsSSB__best_ssb_Index z) /\
  MeasQuantityResults__cond (MeasResultServingCell_r16__resultsSSB__best_ssb_Results z) /\
  MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__cond (MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB z) /\
  True.

Record MeasResultServingCell_r16__Type : Set :=
  make__MeasResultServingCell_r16__Type {
    MeasResultServingCell_r16__resultsSSB_Cell : MeasQuantityResults__Type ;
    MeasResultServingCell_r16__resultsSSB : option MeasResultServingCell_r16__resultsSSB__Type ;
}.
Definition MeasResultServingCell_r16__list := (
 Nor MeasQuantityResults__Type MeasQuantityResults__cond ::
 Opt MeasResultServingCell_r16__resultsSSB__Type MeasResultServingCell_r16__resultsSSB__cond ::
 nil).
Definition MeasResultServingCell_r16__cond z := 
  MeasQuantityResults__cond (MeasResultServingCell_r16__resultsSSB_Cell z) /\
  opt_cond MeasResultServingCell_r16__resultsSSB__cond (MeasResultServingCell_r16__resultsSSB z) /\
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
Definition MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__Format : T_Format Z MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__cond :=
 ranged_int_format (1) (maxNrofSSBs_r16) MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__helper1 MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__helper2.

Opaque MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__cond MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__Format.


Definition MeasResultServingCell_r16__resultsSSB__Format_Type := Eval cbn in seq_format_prod MeasResultServingCell_r16__resultsSSB__list.
Definition MeasResultServingCell_r16__resultsSSB__Format_list : MeasResultServingCell_r16__resultsSSB__Format_Type :=
  (SSB_Index__Format, (MeasQuantityResults__Format, (MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB__Format, unit_format))).
Definition MeasResultServingCell_r16__resultsSSB__list__Format := (*Eval compute in *) seq_format MeasResultServingCell_r16__resultsSSB__list MeasResultServingCell_r16__resultsSSB__Format_list.
Definition MeasResultServingCell_r16__resultsSSB__F1 z :=
  (MeasResultServingCell_r16__resultsSSB__best_ssb_Index z, (MeasResultServingCell_r16__resultsSSB__best_ssb_Results z, (MeasResultServingCell_r16__resultsSSB__numberOfGoodSSB z, tt))).
Definition MeasResultServingCell_r16__resultsSSB__F2 (y : seq_type MeasResultServingCell_r16__resultsSSB__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasResultServingCell_r16__resultsSSB__Type i0 i1 i2
  end.
Lemma MeasResultServingCell_r16__resultsSSB__F1F2_cond (z : MeasResultServingCell_r16__resultsSSB__Type)
  : MeasResultServingCell_r16__resultsSSB__cond z ->
  (seq_cond MeasResultServingCell_r16__resultsSSB__list (MeasResultServingCell_r16__resultsSSB__F1 z)).
intro H. unfold MeasResultServingCell_r16__resultsSSB__cond in H. simpl. auto. Qed.
Lemma MeasResultServingCell_r16__resultsSSB__F1F2_cond2 (z : MeasResultServingCell_r16__resultsSSB__Type)
 : MeasResultServingCell_r16__resultsSSB__F2 (MeasResultServingCell_r16__resultsSSB__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultServingCell_r16__resultsSSB__F2F1_cond (y : seq_type MeasResultServingCell_r16__resultsSSB__list)
  : seq_cond MeasResultServingCell_r16__resultsSSB__list y ->
 (MeasResultServingCell_r16__resultsSSB__cond (MeasResultServingCell_r16__resultsSSB__F2 y)) /\  MeasResultServingCell_r16__resultsSSB__F1 (MeasResultServingCell_r16__resultsSSB__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultServingCell_r16__resultsSSB__cond. simpl in *. auto.
 - simpl. unfold MeasResultServingCell_r16__resultsSSB__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultServingCell_r16__resultsSSB__Format : T_Format MeasResultServingCell_r16__resultsSSB__Type MeasResultServingCell_r16__resultsSSB__cond :=
        proj2_format  MeasResultServingCell_r16__resultsSSB__cond MeasResultServingCell_r16__resultsSSB__list__Format
    MeasResultServingCell_r16__resultsSSB__F1 MeasResultServingCell_r16__resultsSSB__F2 MeasResultServingCell_r16__resultsSSB__F1F2_cond  MeasResultServingCell_r16__resultsSSB__F1F2_cond2 MeasResultServingCell_r16__resultsSSB__F2F1_cond.
Opaque MeasResultServingCell_r16__resultsSSB__cond MeasResultServingCell_r16__resultsSSB__Format.


Definition MeasResultServingCell_r16__Format_Type := Eval cbn in seq_format_prod MeasResultServingCell_r16__list.
Definition MeasResultServingCell_r16__Format_list : MeasResultServingCell_r16__Format_Type :=
  (MeasQuantityResults__Format, (MeasResultServingCell_r16__resultsSSB__Format, unit_format)).
Definition MeasResultServingCell_r16__list__Format := (*Eval compute in *) seq_format MeasResultServingCell_r16__list MeasResultServingCell_r16__Format_list.
Definition MeasResultServingCell_r16__F1 z :=
  (MeasResultServingCell_r16__resultsSSB_Cell z, (MeasResultServingCell_r16__resultsSSB z, tt)).
Definition MeasResultServingCell_r16__F2 (y : seq_type MeasResultServingCell_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultServingCell_r16__Type i0 i1
  end.
Lemma MeasResultServingCell_r16__F1F2_cond (z : MeasResultServingCell_r16__Type)
  : MeasResultServingCell_r16__cond z ->
  (seq_cond MeasResultServingCell_r16__list (MeasResultServingCell_r16__F1 z)).
intro H. unfold MeasResultServingCell_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultServingCell_r16__F1F2_cond2 (z : MeasResultServingCell_r16__Type)
 : MeasResultServingCell_r16__F2 (MeasResultServingCell_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultServingCell_r16__F2F1_cond (y : seq_type MeasResultServingCell_r16__list)
  : seq_cond MeasResultServingCell_r16__list y ->
 (MeasResultServingCell_r16__cond (MeasResultServingCell_r16__F2 y)) /\  MeasResultServingCell_r16__F1 (MeasResultServingCell_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultServingCell_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultServingCell_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultServingCell_r16__Format : T_Format MeasResultServingCell_r16__Type MeasResultServingCell_r16__cond :=
        proj2_format  MeasResultServingCell_r16__cond MeasResultServingCell_r16__list__Format
    MeasResultServingCell_r16__F1 MeasResultServingCell_r16__F2 MeasResultServingCell_r16__F1F2_cond  MeasResultServingCell_r16__F1F2_cond2 MeasResultServingCell_r16__F2F1_cond.
Opaque MeasResultServingCell_r16__cond MeasResultServingCell_r16__Format.

