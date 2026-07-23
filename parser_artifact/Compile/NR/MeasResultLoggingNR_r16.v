Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.MeasQuantityResults.

Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

Lemma MeasResultLoggingNR_r16__numberOfGoodSSB_r16__helper1 : (1 <= maxNrofSSBs_r16)%Z. unfold maxNrofSSBs_r16.
 lia. Qed.
Lemma MeasResultLoggingNR_r16__numberOfGoodSSB_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSSBs_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSSBs_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultLoggingNR_r16__numberOfGoodSSB_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultLoggingNR_r16__numberOfGoodSSB_r16__Type := Z.
Definition MeasResultLoggingNR_r16__numberOfGoodSSB_r16__cond := (fun z => (1 <= z <= maxNrofSSBs_r16)%Z).
Record MeasResultLoggingNR_r16__Type : Set :=
  make__MeasResultLoggingNR_r16__Type {
    MeasResultLoggingNR_r16__physCellId_r16 : PhysCellId__Type ;
    MeasResultLoggingNR_r16__resultsSSB_Cell_r16 : MeasQuantityResults__Type ;
    MeasResultLoggingNR_r16__numberOfGoodSSB_r16 : option Z ;
}.
Definition MeasResultLoggingNR_r16__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor MeasQuantityResults__Type MeasQuantityResults__cond ::
 Opt Z MeasResultLoggingNR_r16__numberOfGoodSSB_r16__cond ::
 nil).
Definition MeasResultLoggingNR_r16__cond z := 
  PhysCellId__cond (MeasResultLoggingNR_r16__physCellId_r16 z) /\
  MeasQuantityResults__cond (MeasResultLoggingNR_r16__resultsSSB_Cell_r16 z) /\
  opt_cond MeasResultLoggingNR_r16__numberOfGoodSSB_r16__cond (MeasResultLoggingNR_r16__numberOfGoodSSB_r16 z) /\
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
Definition MeasResultLoggingNR_r16__numberOfGoodSSB_r16__Format : T_Format Z MeasResultLoggingNR_r16__numberOfGoodSSB_r16__cond :=
 ranged_int_format (1) (maxNrofSSBs_r16) MeasResultLoggingNR_r16__numberOfGoodSSB_r16__helper1 MeasResultLoggingNR_r16__numberOfGoodSSB_r16__helper2.

Opaque MeasResultLoggingNR_r16__numberOfGoodSSB_r16__cond MeasResultLoggingNR_r16__numberOfGoodSSB_r16__Format.


Definition MeasResultLoggingNR_r16__Format_Type := Eval cbn in seq_format_prod MeasResultLoggingNR_r16__list.
Definition MeasResultLoggingNR_r16__Format_list : MeasResultLoggingNR_r16__Format_Type :=
  (PhysCellId__Format, (MeasQuantityResults__Format, (MeasResultLoggingNR_r16__numberOfGoodSSB_r16__Format, unit_format))).
Definition MeasResultLoggingNR_r16__list__Format := (*Eval compute in *) seq_format MeasResultLoggingNR_r16__list MeasResultLoggingNR_r16__Format_list.
Definition MeasResultLoggingNR_r16__F1 z :=
  (MeasResultLoggingNR_r16__physCellId_r16 z, (MeasResultLoggingNR_r16__resultsSSB_Cell_r16 z, (MeasResultLoggingNR_r16__numberOfGoodSSB_r16 z, tt))).
Definition MeasResultLoggingNR_r16__F2 (y : seq_type MeasResultLoggingNR_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasResultLoggingNR_r16__Type i0 i1 i2
  end.
Lemma MeasResultLoggingNR_r16__F1F2_cond (z : MeasResultLoggingNR_r16__Type)
  : MeasResultLoggingNR_r16__cond z ->
  (seq_cond MeasResultLoggingNR_r16__list (MeasResultLoggingNR_r16__F1 z)).
intro H. unfold MeasResultLoggingNR_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultLoggingNR_r16__F1F2_cond2 (z : MeasResultLoggingNR_r16__Type)
 : MeasResultLoggingNR_r16__F2 (MeasResultLoggingNR_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultLoggingNR_r16__F2F1_cond (y : seq_type MeasResultLoggingNR_r16__list)
  : seq_cond MeasResultLoggingNR_r16__list y ->
 (MeasResultLoggingNR_r16__cond (MeasResultLoggingNR_r16__F2 y)) /\  MeasResultLoggingNR_r16__F1 (MeasResultLoggingNR_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultLoggingNR_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultLoggingNR_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultLoggingNR_r16__Format : T_Format MeasResultLoggingNR_r16__Type MeasResultLoggingNR_r16__cond :=
        proj2_format  MeasResultLoggingNR_r16__cond MeasResultLoggingNR_r16__list__Format
    MeasResultLoggingNR_r16__F1 MeasResultLoggingNR_r16__F2 MeasResultLoggingNR_r16__F1F2_cond  MeasResultLoggingNR_r16__F1F2_cond2 MeasResultLoggingNR_r16__F2F1_cond.
Opaque MeasResultLoggingNR_r16__cond MeasResultLoggingNR_r16__Format.

