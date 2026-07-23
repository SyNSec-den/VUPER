Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Lemma MeasResultCellSFTD_NR__sfn_OffsetResult__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma MeasResultCellSFTD_NR__sfn_OffsetResult__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultCellSFTD_NR__sfn_OffsetResult__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultCellSFTD_NR__sfn_OffsetResult__Type := Z.
Definition MeasResultCellSFTD_NR__sfn_OffsetResult__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma MeasResultCellSFTD_NR__frameBoundaryOffsetResult__helper1 : (-30720 <= 30719)%Z.  lia. Qed.
Lemma MeasResultCellSFTD_NR__frameBoundaryOffsetResult__helper2 : to_bit_sz (Z.to_nat (30719 - -30720)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (30719 - -30720))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultCellSFTD_NR__frameBoundaryOffsetResult__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultCellSFTD_NR__frameBoundaryOffsetResult__Type := Z.
Definition MeasResultCellSFTD_NR__frameBoundaryOffsetResult__cond := (fun z => (-30720 <= z <= 30719)%Z).
Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Record MeasResultCellSFTD_NR__Type : Set :=
  make__MeasResultCellSFTD_NR__Type {
    MeasResultCellSFTD_NR__physCellId : PhysCellId__Type ;
    MeasResultCellSFTD_NR__sfn_OffsetResult : Z ;
    MeasResultCellSFTD_NR__frameBoundaryOffsetResult : Z ;
    MeasResultCellSFTD_NR__rsrp_Result : option RSRP_Range__Type ;
}.
Definition MeasResultCellSFTD_NR__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor Z MeasResultCellSFTD_NR__sfn_OffsetResult__cond ::
 Nor Z MeasResultCellSFTD_NR__frameBoundaryOffsetResult__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 nil).
Definition MeasResultCellSFTD_NR__cond z := 
  PhysCellId__cond (MeasResultCellSFTD_NR__physCellId z) /\
  MeasResultCellSFTD_NR__sfn_OffsetResult__cond (MeasResultCellSFTD_NR__sfn_OffsetResult z) /\
  MeasResultCellSFTD_NR__frameBoundaryOffsetResult__cond (MeasResultCellSFTD_NR__frameBoundaryOffsetResult z) /\
  opt_cond RSRP_Range__cond (MeasResultCellSFTD_NR__rsrp_Result z) /\
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
Definition MeasResultCellSFTD_NR__sfn_OffsetResult__Format : T_Format Z MeasResultCellSFTD_NR__sfn_OffsetResult__cond :=
 ranged_int_format (0) (1023) MeasResultCellSFTD_NR__sfn_OffsetResult__helper1 MeasResultCellSFTD_NR__sfn_OffsetResult__helper2.

Opaque MeasResultCellSFTD_NR__sfn_OffsetResult__cond MeasResultCellSFTD_NR__sfn_OffsetResult__Format.

Definition MeasResultCellSFTD_NR__frameBoundaryOffsetResult__Format : T_Format Z MeasResultCellSFTD_NR__frameBoundaryOffsetResult__cond :=
 ranged_int_format (-30720) (30719) MeasResultCellSFTD_NR__frameBoundaryOffsetResult__helper1 MeasResultCellSFTD_NR__frameBoundaryOffsetResult__helper2.

Opaque MeasResultCellSFTD_NR__frameBoundaryOffsetResult__cond MeasResultCellSFTD_NR__frameBoundaryOffsetResult__Format.


Definition MeasResultCellSFTD_NR__Format_Type := Eval cbn in seq_format_prod MeasResultCellSFTD_NR__list.
Definition MeasResultCellSFTD_NR__Format_list : MeasResultCellSFTD_NR__Format_Type :=
  (PhysCellId__Format, (MeasResultCellSFTD_NR__sfn_OffsetResult__Format, (MeasResultCellSFTD_NR__frameBoundaryOffsetResult__Format, (RSRP_Range__Format, unit_format)))).
Definition MeasResultCellSFTD_NR__list__Format := (*Eval compute in *) seq_format MeasResultCellSFTD_NR__list MeasResultCellSFTD_NR__Format_list.
Definition MeasResultCellSFTD_NR__F1 z :=
  (MeasResultCellSFTD_NR__physCellId z, (MeasResultCellSFTD_NR__sfn_OffsetResult z, (MeasResultCellSFTD_NR__frameBoundaryOffsetResult z, (MeasResultCellSFTD_NR__rsrp_Result z, tt)))).
Definition MeasResultCellSFTD_NR__F2 (y : seq_type MeasResultCellSFTD_NR__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasResultCellSFTD_NR__Type i0 i1 i2 i3
  end.
Lemma MeasResultCellSFTD_NR__F1F2_cond (z : MeasResultCellSFTD_NR__Type)
  : MeasResultCellSFTD_NR__cond z ->
  (seq_cond MeasResultCellSFTD_NR__list (MeasResultCellSFTD_NR__F1 z)).
intro H. unfold MeasResultCellSFTD_NR__cond in H. simpl. auto. Qed.
Lemma MeasResultCellSFTD_NR__F1F2_cond2 (z : MeasResultCellSFTD_NR__Type)
 : MeasResultCellSFTD_NR__F2 (MeasResultCellSFTD_NR__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultCellSFTD_NR__F2F1_cond (y : seq_type MeasResultCellSFTD_NR__list)
  : seq_cond MeasResultCellSFTD_NR__list y ->
 (MeasResultCellSFTD_NR__cond (MeasResultCellSFTD_NR__F2 y)) /\  MeasResultCellSFTD_NR__F1 (MeasResultCellSFTD_NR__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultCellSFTD_NR__cond. simpl in *. auto.
 - simpl. unfold MeasResultCellSFTD_NR__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultCellSFTD_NR__Format : T_Format MeasResultCellSFTD_NR__Type MeasResultCellSFTD_NR__cond :=
        proj2_format  MeasResultCellSFTD_NR__cond MeasResultCellSFTD_NR__list__Format
    MeasResultCellSFTD_NR__F1 MeasResultCellSFTD_NR__F2 MeasResultCellSFTD_NR__F1F2_cond  MeasResultCellSFTD_NR__F1F2_cond2 MeasResultCellSFTD_NR__F2F1_cond.
Opaque MeasResultCellSFTD_NR__cond MeasResultCellSFTD_NR__Format.

