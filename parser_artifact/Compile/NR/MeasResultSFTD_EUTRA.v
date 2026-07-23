Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Lemma MeasResultSFTD_EUTRA__sfn_OffsetResult__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma MeasResultSFTD_EUTRA__sfn_OffsetResult__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultSFTD_EUTRA__sfn_OffsetResult__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultSFTD_EUTRA__sfn_OffsetResult__Type := Z.
Definition MeasResultSFTD_EUTRA__sfn_OffsetResult__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__helper1 : (-30720 <= 30719)%Z.  lia. Qed.
Lemma MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__helper2 : to_bit_sz (Z.to_nat (30719 - -30720)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (30719 - -30720))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__Type := Z.
Definition MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__cond := (fun z => (-30720 <= z <= 30719)%Z).
Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Record MeasResultSFTD_EUTRA__Type : Set :=
  make__MeasResultSFTD_EUTRA__Type {
    MeasResultSFTD_EUTRA__eutra_PhysCellId : EUTRA_PhysCellId__Type ;
    MeasResultSFTD_EUTRA__sfn_OffsetResult : Z ;
    MeasResultSFTD_EUTRA__frameBoundaryOffsetResult : Z ;
    MeasResultSFTD_EUTRA__rsrp_Result : option RSRP_Range__Type ;
}.
Definition MeasResultSFTD_EUTRA__list := (
 Nor EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
 Nor Z MeasResultSFTD_EUTRA__sfn_OffsetResult__cond ::
 Nor Z MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 nil).
Definition MeasResultSFTD_EUTRA__cond z := 
  EUTRA_PhysCellId__cond (MeasResultSFTD_EUTRA__eutra_PhysCellId z) /\
  MeasResultSFTD_EUTRA__sfn_OffsetResult__cond (MeasResultSFTD_EUTRA__sfn_OffsetResult z) /\
  MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__cond (MeasResultSFTD_EUTRA__frameBoundaryOffsetResult z) /\
  opt_cond RSRP_Range__cond (MeasResultSFTD_EUTRA__rsrp_Result z) /\
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
Definition MeasResultSFTD_EUTRA__sfn_OffsetResult__Format : T_Format Z MeasResultSFTD_EUTRA__sfn_OffsetResult__cond :=
 ranged_int_format (0) (1023) MeasResultSFTD_EUTRA__sfn_OffsetResult__helper1 MeasResultSFTD_EUTRA__sfn_OffsetResult__helper2.

Opaque MeasResultSFTD_EUTRA__sfn_OffsetResult__cond MeasResultSFTD_EUTRA__sfn_OffsetResult__Format.

Definition MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__Format : T_Format Z MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__cond :=
 ranged_int_format (-30720) (30719) MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__helper1 MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__helper2.

Opaque MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__cond MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__Format.


Definition MeasResultSFTD_EUTRA__Format_Type := Eval cbn in seq_format_prod MeasResultSFTD_EUTRA__list.
Definition MeasResultSFTD_EUTRA__Format_list : MeasResultSFTD_EUTRA__Format_Type :=
  (EUTRA_PhysCellId__Format, (MeasResultSFTD_EUTRA__sfn_OffsetResult__Format, (MeasResultSFTD_EUTRA__frameBoundaryOffsetResult__Format, (RSRP_Range__Format, unit_format)))).
Definition MeasResultSFTD_EUTRA__list__Format := (*Eval compute in *) seq_format MeasResultSFTD_EUTRA__list MeasResultSFTD_EUTRA__Format_list.
Definition MeasResultSFTD_EUTRA__F1 z :=
  (MeasResultSFTD_EUTRA__eutra_PhysCellId z, (MeasResultSFTD_EUTRA__sfn_OffsetResult z, (MeasResultSFTD_EUTRA__frameBoundaryOffsetResult z, (MeasResultSFTD_EUTRA__rsrp_Result z, tt)))).
Definition MeasResultSFTD_EUTRA__F2 (y : seq_type MeasResultSFTD_EUTRA__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasResultSFTD_EUTRA__Type i0 i1 i2 i3
  end.
Lemma MeasResultSFTD_EUTRA__F1F2_cond (z : MeasResultSFTD_EUTRA__Type)
  : MeasResultSFTD_EUTRA__cond z ->
  (seq_cond MeasResultSFTD_EUTRA__list (MeasResultSFTD_EUTRA__F1 z)).
intro H. unfold MeasResultSFTD_EUTRA__cond in H. simpl. auto. Qed.
Lemma MeasResultSFTD_EUTRA__F1F2_cond2 (z : MeasResultSFTD_EUTRA__Type)
 : MeasResultSFTD_EUTRA__F2 (MeasResultSFTD_EUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultSFTD_EUTRA__F2F1_cond (y : seq_type MeasResultSFTD_EUTRA__list)
  : seq_cond MeasResultSFTD_EUTRA__list y ->
 (MeasResultSFTD_EUTRA__cond (MeasResultSFTD_EUTRA__F2 y)) /\  MeasResultSFTD_EUTRA__F1 (MeasResultSFTD_EUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultSFTD_EUTRA__cond. simpl in *. auto.
 - simpl. unfold MeasResultSFTD_EUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultSFTD_EUTRA__Format : T_Format MeasResultSFTD_EUTRA__Type MeasResultSFTD_EUTRA__cond :=
        proj2_format  MeasResultSFTD_EUTRA__cond MeasResultSFTD_EUTRA__list__Format
    MeasResultSFTD_EUTRA__F1 MeasResultSFTD_EUTRA__F2 MeasResultSFTD_EUTRA__F1F2_cond  MeasResultSFTD_EUTRA__F1F2_cond2 MeasResultSFTD_EUTRA__F2F1_cond.
Opaque MeasResultSFTD_EUTRA__cond MeasResultSFTD_EUTRA__Format.

