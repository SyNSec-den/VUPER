Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.InterFreqNeighCellList_v1610.

Opaque InterFreqNeighCellList_v1610__cond InterFreqNeighCellList_v1610__Format.

Require Import NR.SSB_MTC2_LP_r16.

Opaque SSB_MTC2_LP_r16__cond SSB_MTC2_LP_r16__Format.

Require Import NR.InterFreqAllowedCellList_r16.

Opaque InterFreqAllowedCellList_r16__cond InterFreqAllowedCellList_r16__Format.

Require Import NR.SSB_PositionQCL_Relation_r16.

Opaque SSB_PositionQCL_Relation_r16__cond SSB_PositionQCL_Relation_r16__Format.

Require Import NR.InterFreqCAG_CellListPerPLMN_r16.

Opaque InterFreqCAG_CellListPerPLMN_r16__cond InterFreqCAG_CellListPerPLMN_r16__Format.

Definition InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__Type := list InterFreqCAG_CellListPerPLMN_r16__Type.

Lemma InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__helper1 : (0 <= 1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__cond (z : InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxPLMN)%Z /\ (list_and InterFreqCAG_CellListPerPLMN_r16__cond z) .

Record InterFreqCarrierFreqInfo_v1610__Type : Set :=
  make__InterFreqCarrierFreqInfo_v1610__Type {
    InterFreqCarrierFreqInfo_v1610__interFreqNeighCellList_v1610 : option InterFreqNeighCellList_v1610__Type ;
    InterFreqCarrierFreqInfo_v1610__smtc2_LP_r16 : option SSB_MTC2_LP_r16__Type ;
    InterFreqCarrierFreqInfo_v1610__interFreqAllowedCellList_r16 : option InterFreqAllowedCellList_r16__Type ;
    InterFreqCarrierFreqInfo_v1610__ssb_PositionQCL_Common_r16 : option SSB_PositionQCL_Relation_r16__Type ;
    InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16 : option InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__Type ;
}.
Definition InterFreqCarrierFreqInfo_v1610__list := (
 Opt InterFreqNeighCellList_v1610__Type InterFreqNeighCellList_v1610__cond ::
 Opt SSB_MTC2_LP_r16__Type SSB_MTC2_LP_r16__cond ::
 Opt InterFreqAllowedCellList_r16__Type InterFreqAllowedCellList_r16__cond ::
 Opt SSB_PositionQCL_Relation_r16__Type SSB_PositionQCL_Relation_r16__cond ::
 Opt InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__Type InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__cond ::
 nil).
Definition InterFreqCarrierFreqInfo_v1610__cond z := 
  opt_cond InterFreqNeighCellList_v1610__cond (InterFreqCarrierFreqInfo_v1610__interFreqNeighCellList_v1610 z) /\
  opt_cond SSB_MTC2_LP_r16__cond (InterFreqCarrierFreqInfo_v1610__smtc2_LP_r16 z) /\
  opt_cond InterFreqAllowedCellList_r16__cond (InterFreqCarrierFreqInfo_v1610__interFreqAllowedCellList_r16 z) /\
  opt_cond SSB_PositionQCL_Relation_r16__cond (InterFreqCarrierFreqInfo_v1610__ssb_PositionQCL_Common_r16 z) /\
  opt_cond InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__cond (InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16 z) /\
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
Definition InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__Format : T_Format InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__Type InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__cond := seq_of_format InterFreqCAG_CellListPerPLMN_r16__Format 1 maxPLMN InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__helper1 InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__helper2.

Opaque InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__cond InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__Format.


Definition InterFreqCarrierFreqInfo_v1610__Format_Type := Eval cbn in seq_format_prod InterFreqCarrierFreqInfo_v1610__list.
Definition InterFreqCarrierFreqInfo_v1610__Format_list : InterFreqCarrierFreqInfo_v1610__Format_Type :=
  (InterFreqNeighCellList_v1610__Format, (SSB_MTC2_LP_r16__Format, (InterFreqAllowedCellList_r16__Format, (SSB_PositionQCL_Relation_r16__Format, (InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16__Format, unit_format))))).
Definition InterFreqCarrierFreqInfo_v1610__list__Format := (*Eval compute in *) seq_format InterFreqCarrierFreqInfo_v1610__list InterFreqCarrierFreqInfo_v1610__Format_list.
Definition InterFreqCarrierFreqInfo_v1610__F1 z :=
  (InterFreqCarrierFreqInfo_v1610__interFreqNeighCellList_v1610 z, (InterFreqCarrierFreqInfo_v1610__smtc2_LP_r16 z, (InterFreqCarrierFreqInfo_v1610__interFreqAllowedCellList_r16 z, (InterFreqCarrierFreqInfo_v1610__ssb_PositionQCL_Common_r16 z, (InterFreqCarrierFreqInfo_v1610__interFreqCAG_CellList_r16 z, tt))))).
Definition InterFreqCarrierFreqInfo_v1610__F2 (y : seq_type InterFreqCarrierFreqInfo_v1610__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__InterFreqCarrierFreqInfo_v1610__Type i0 i1 i2 i3 i4
  end.
Lemma InterFreqCarrierFreqInfo_v1610__F1F2_cond (z : InterFreqCarrierFreqInfo_v1610__Type)
  : InterFreqCarrierFreqInfo_v1610__cond z ->
  (seq_cond InterFreqCarrierFreqInfo_v1610__list (InterFreqCarrierFreqInfo_v1610__F1 z)).
intro H. unfold InterFreqCarrierFreqInfo_v1610__cond in H. simpl. auto. Qed.
Lemma InterFreqCarrierFreqInfo_v1610__F1F2_cond2 (z : InterFreqCarrierFreqInfo_v1610__Type)
 : InterFreqCarrierFreqInfo_v1610__F2 (InterFreqCarrierFreqInfo_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma InterFreqCarrierFreqInfo_v1610__F2F1_cond (y : seq_type InterFreqCarrierFreqInfo_v1610__list)
  : seq_cond InterFreqCarrierFreqInfo_v1610__list y ->
 (InterFreqCarrierFreqInfo_v1610__cond (InterFreqCarrierFreqInfo_v1610__F2 y)) /\  InterFreqCarrierFreqInfo_v1610__F1 (InterFreqCarrierFreqInfo_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold InterFreqCarrierFreqInfo_v1610__cond. simpl in *. auto.
 - simpl. unfold InterFreqCarrierFreqInfo_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition InterFreqCarrierFreqInfo_v1610__Format : T_Format InterFreqCarrierFreqInfo_v1610__Type InterFreqCarrierFreqInfo_v1610__cond :=
        proj2_format  InterFreqCarrierFreqInfo_v1610__cond InterFreqCarrierFreqInfo_v1610__list__Format
    InterFreqCarrierFreqInfo_v1610__F1 InterFreqCarrierFreqInfo_v1610__F2 InterFreqCarrierFreqInfo_v1610__F1F2_cond  InterFreqCarrierFreqInfo_v1610__F1F2_cond2 InterFreqCarrierFreqInfo_v1610__F2F1_cond.
Opaque InterFreqCarrierFreqInfo_v1610__cond InterFreqCarrierFreqInfo_v1610__Format.

