Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TMGI_r17.

Opaque TMGI_r17__cond TMGI_r17__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.MRB_ListBroadcast_r17.

Opaque MRB_ListBroadcast_r17__cond MRB_ListBroadcast_r17__Format.

Require Import NR.DRX_ConfigPTM_Index_r17.

Opaque DRX_ConfigPTM_Index_r17__cond DRX_ConfigPTM_Index_r17__Format.

Definition MBS_SessionInfo_r17__mtch_NeighbourCell_r17__Type := bit_string_fixed.
Definition MBS_SessionInfo_r17__mtch_NeighbourCell_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat maxNeighCellMBS_r17 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.PDSCH_ConfigIndex_r17.

Opaque PDSCH_ConfigIndex_r17__cond PDSCH_ConfigIndex_r17__Format.

Require Import NR.MTCH_SSB_MappingWindowIndex_r17.

Opaque MTCH_SSB_MappingWindowIndex_r17__cond MTCH_SSB_MappingWindowIndex_r17__Format.

Record MBS_SessionInfo_r17__Type : Set :=
  make__MBS_SessionInfo_r17__Type {
    MBS_SessionInfo_r17__mbs_SessionId_r17 : TMGI_r17__Type ;
    MBS_SessionInfo_r17__g_RNTI_r17 : RNTI_Value__Type ;
    MBS_SessionInfo_r17__mrb_ListBroadcast_r17 : MRB_ListBroadcast_r17__Type ;
    MBS_SessionInfo_r17__mtch_SchedulingInfo_r17 : option DRX_ConfigPTM_Index_r17__Type ;
    MBS_SessionInfo_r17__mtch_NeighbourCell_r17 : option MBS_SessionInfo_r17__mtch_NeighbourCell_r17__Type ;
    MBS_SessionInfo_r17__pdsch_ConfigIndex_r17 : option PDSCH_ConfigIndex_r17__Type ;
    MBS_SessionInfo_r17__mtch_SSB_MappingWindowIndex_r17 : option MTCH_SSB_MappingWindowIndex_r17__Type ;
}.
Definition MBS_SessionInfo_r17__list := (
 Nor TMGI_r17__Type TMGI_r17__cond ::
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Nor MRB_ListBroadcast_r17__Type MRB_ListBroadcast_r17__cond ::
 Opt DRX_ConfigPTM_Index_r17__Type DRX_ConfigPTM_Index_r17__cond ::
 Opt MBS_SessionInfo_r17__mtch_NeighbourCell_r17__Type MBS_SessionInfo_r17__mtch_NeighbourCell_r17__cond ::
 Opt PDSCH_ConfigIndex_r17__Type PDSCH_ConfigIndex_r17__cond ::
 Opt MTCH_SSB_MappingWindowIndex_r17__Type MTCH_SSB_MappingWindowIndex_r17__cond ::
 nil).
Definition MBS_SessionInfo_r17__cond z := 
  TMGI_r17__cond (MBS_SessionInfo_r17__mbs_SessionId_r17 z) /\
  RNTI_Value__cond (MBS_SessionInfo_r17__g_RNTI_r17 z) /\
  MRB_ListBroadcast_r17__cond (MBS_SessionInfo_r17__mrb_ListBroadcast_r17 z) /\
  opt_cond DRX_ConfigPTM_Index_r17__cond (MBS_SessionInfo_r17__mtch_SchedulingInfo_r17 z) /\
  opt_cond MBS_SessionInfo_r17__mtch_NeighbourCell_r17__cond (MBS_SessionInfo_r17__mtch_NeighbourCell_r17 z) /\
  opt_cond PDSCH_ConfigIndex_r17__cond (MBS_SessionInfo_r17__pdsch_ConfigIndex_r17 z) /\
  opt_cond MTCH_SSB_MappingWindowIndex_r17__cond (MBS_SessionInfo_r17__mtch_SSB_MappingWindowIndex_r17 z) /\
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
Definition MBS_SessionInfo_r17__mtch_NeighbourCell_r17__Format : T_Format MBS_SessionInfo_r17__mtch_NeighbourCell_r17__Type MBS_SessionInfo_r17__mtch_NeighbourCell_r17__cond := (* Eval compute in *) bit_string_fixed_format maxNeighCellMBS_r17.
Opaque MBS_SessionInfo_r17__mtch_NeighbourCell_r17__cond MBS_SessionInfo_r17__mtch_NeighbourCell_r17__Format.


Definition MBS_SessionInfo_r17__Format_Type := Eval cbn in seq_format_prod MBS_SessionInfo_r17__list.
Definition MBS_SessionInfo_r17__Format_list : MBS_SessionInfo_r17__Format_Type :=
  (TMGI_r17__Format, (RNTI_Value__Format, (MRB_ListBroadcast_r17__Format, (DRX_ConfigPTM_Index_r17__Format, (MBS_SessionInfo_r17__mtch_NeighbourCell_r17__Format, (PDSCH_ConfigIndex_r17__Format, (MTCH_SSB_MappingWindowIndex_r17__Format, unit_format))))))).
Definition MBS_SessionInfo_r17__list__Format := (*Eval compute in *) seq_format MBS_SessionInfo_r17__list MBS_SessionInfo_r17__Format_list.
Definition MBS_SessionInfo_r17__F1 z :=
  (MBS_SessionInfo_r17__mbs_SessionId_r17 z, (MBS_SessionInfo_r17__g_RNTI_r17 z, (MBS_SessionInfo_r17__mrb_ListBroadcast_r17 z, (MBS_SessionInfo_r17__mtch_SchedulingInfo_r17 z, (MBS_SessionInfo_r17__mtch_NeighbourCell_r17 z, (MBS_SessionInfo_r17__pdsch_ConfigIndex_r17 z, (MBS_SessionInfo_r17__mtch_SSB_MappingWindowIndex_r17 z, tt))))))).
Definition MBS_SessionInfo_r17__F2 (y : seq_type MBS_SessionInfo_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__MBS_SessionInfo_r17__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma MBS_SessionInfo_r17__F1F2_cond (z : MBS_SessionInfo_r17__Type)
  : MBS_SessionInfo_r17__cond z ->
  (seq_cond MBS_SessionInfo_r17__list (MBS_SessionInfo_r17__F1 z)).
intro H. unfold MBS_SessionInfo_r17__cond in H. simpl. auto. Qed.
Lemma MBS_SessionInfo_r17__F1F2_cond2 (z : MBS_SessionInfo_r17__Type)
 : MBS_SessionInfo_r17__F2 (MBS_SessionInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MBS_SessionInfo_r17__F2F1_cond (y : seq_type MBS_SessionInfo_r17__list)
  : seq_cond MBS_SessionInfo_r17__list y ->
 (MBS_SessionInfo_r17__cond (MBS_SessionInfo_r17__F2 y)) /\  MBS_SessionInfo_r17__F1 (MBS_SessionInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MBS_SessionInfo_r17__cond. simpl in *. auto.
 - simpl. unfold MBS_SessionInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MBS_SessionInfo_r17__Format : T_Format MBS_SessionInfo_r17__Type MBS_SessionInfo_r17__cond :=
        proj2_format  MBS_SessionInfo_r17__cond MBS_SessionInfo_r17__list__Format
    MBS_SessionInfo_r17__F1 MBS_SessionInfo_r17__F2 MBS_SessionInfo_r17__F1F2_cond  MBS_SessionInfo_r17__F1F2_cond2 MBS_SessionInfo_r17__F2F1_cond.
Opaque MBS_SessionInfo_r17__cond MBS_SessionInfo_r17__Format.

