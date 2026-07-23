Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Require Import NR.EUTRA_Q_OffsetRange.

Opaque EUTRA_Q_OffsetRange__cond EUTRA_Q_OffsetRange__Format.

Lemma EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__Type := Z.
Definition EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__cond := (fun z => (1 <= z <= 8)%Z).
Lemma EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__Type := Z.
Definition EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__cond := (fun z => (1 <= z <= 8)%Z).
Record EUTRA_FreqNeighCellInfo__Type : Set :=
  make__EUTRA_FreqNeighCellInfo__Type {
    EUTRA_FreqNeighCellInfo__physCellId : EUTRA_PhysCellId__Type ;
    EUTRA_FreqNeighCellInfo__dummy : EUTRA_Q_OffsetRange__Type ;
    EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell : option Z ;
    EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell : option Z ;
}.
Definition EUTRA_FreqNeighCellInfo__list := (
 Nor EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
 Nor EUTRA_Q_OffsetRange__Type EUTRA_Q_OffsetRange__cond ::
 Opt Z EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__cond ::
 Opt Z EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__cond ::
 nil).
Definition EUTRA_FreqNeighCellInfo__cond z := 
  EUTRA_PhysCellId__cond (EUTRA_FreqNeighCellInfo__physCellId z) /\
  EUTRA_Q_OffsetRange__cond (EUTRA_FreqNeighCellInfo__dummy z) /\
  opt_cond EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__cond (EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell z) /\
  opt_cond EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__cond (EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell z) /\
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
Definition EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__Format : T_Format Z EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__cond :=
 ranged_int_format (1) (8) EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__helper1 EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__helper2.

Opaque EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__cond EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__Format.

Definition EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__Format : T_Format Z EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__cond :=
 ranged_int_format (1) (8) EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__helper1 EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__helper2.

Opaque EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__cond EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__Format.


Definition EUTRA_FreqNeighCellInfo__Format_Type := Eval cbn in seq_format_prod EUTRA_FreqNeighCellInfo__list.
Definition EUTRA_FreqNeighCellInfo__Format_list : EUTRA_FreqNeighCellInfo__Format_Type :=
  (EUTRA_PhysCellId__Format, (EUTRA_Q_OffsetRange__Format, (EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell__Format, (EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell__Format, unit_format)))).
Definition EUTRA_FreqNeighCellInfo__list__Format := (*Eval compute in *) seq_format EUTRA_FreqNeighCellInfo__list EUTRA_FreqNeighCellInfo__Format_list.
Definition EUTRA_FreqNeighCellInfo__F1 z :=
  (EUTRA_FreqNeighCellInfo__physCellId z, (EUTRA_FreqNeighCellInfo__dummy z, (EUTRA_FreqNeighCellInfo__q_RxLevMinOffsetCell z, (EUTRA_FreqNeighCellInfo__q_QualMinOffsetCell z, tt)))).
Definition EUTRA_FreqNeighCellInfo__F2 (y : seq_type EUTRA_FreqNeighCellInfo__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__EUTRA_FreqNeighCellInfo__Type i0 i1 i2 i3
  end.
Lemma EUTRA_FreqNeighCellInfo__F1F2_cond (z : EUTRA_FreqNeighCellInfo__Type)
  : EUTRA_FreqNeighCellInfo__cond z ->
  (seq_cond EUTRA_FreqNeighCellInfo__list (EUTRA_FreqNeighCellInfo__F1 z)).
intro H. unfold EUTRA_FreqNeighCellInfo__cond in H. simpl. auto. Qed.
Lemma EUTRA_FreqNeighCellInfo__F1F2_cond2 (z : EUTRA_FreqNeighCellInfo__Type)
 : EUTRA_FreqNeighCellInfo__F2 (EUTRA_FreqNeighCellInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EUTRA_FreqNeighCellInfo__F2F1_cond (y : seq_type EUTRA_FreqNeighCellInfo__list)
  : seq_cond EUTRA_FreqNeighCellInfo__list y ->
 (EUTRA_FreqNeighCellInfo__cond (EUTRA_FreqNeighCellInfo__F2 y)) /\  EUTRA_FreqNeighCellInfo__F1 (EUTRA_FreqNeighCellInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EUTRA_FreqNeighCellInfo__cond. simpl in *. auto.
 - simpl. unfold EUTRA_FreqNeighCellInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EUTRA_FreqNeighCellInfo__Format : T_Format EUTRA_FreqNeighCellInfo__Type EUTRA_FreqNeighCellInfo__cond :=
        proj2_format  EUTRA_FreqNeighCellInfo__cond EUTRA_FreqNeighCellInfo__list__Format
    EUTRA_FreqNeighCellInfo__F1 EUTRA_FreqNeighCellInfo__F2 EUTRA_FreqNeighCellInfo__F1F2_cond  EUTRA_FreqNeighCellInfo__F1F2_cond2 EUTRA_FreqNeighCellInfo__F2F1_cond.
Opaque EUTRA_FreqNeighCellInfo__cond EUTRA_FreqNeighCellInfo__Format.

