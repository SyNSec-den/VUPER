Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MBS_SessionInfoList_r17.

Opaque MBS_SessionInfoList_r17__cond MBS_SessionInfoList_r17__Format.

Require Import NR.MBS_NeighbourCellList_r17.

Opaque MBS_NeighbourCellList_r17__cond MBS_NeighbourCellList_r17__Format.

Require Import NR.DRX_ConfigPTM_r17.

Opaque DRX_ConfigPTM_r17__cond DRX_ConfigPTM_r17__Format.

Definition MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__Type := list DRX_ConfigPTM_r17__Type.

Lemma MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__helper1 : (0 <= 1 <= maxNrofDRX_ConfigPTM_r17)%Z. unfold maxNrofDRX_ConfigPTM_r17.
 lia. Qed.
Lemma MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofDRX_ConfigPTM_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofDRX_ConfigPTM_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__cond (z : MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofDRX_ConfigPTM_r17)%Z /\ (list_and DRX_ConfigPTM_r17__cond z) .

Require Import NR.PDSCH_ConfigBroadcast_r17.

Opaque PDSCH_ConfigBroadcast_r17__cond PDSCH_ConfigBroadcast_r17__Format.

Require Import NR.MTCH_SSB_MappingWindowList_r17.

Opaque MTCH_SSB_MappingWindowList_r17__cond MTCH_SSB_MappingWindowList_r17__Format.

Record MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type : Set := make__MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type {}.
Definition MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__cond (z : MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type) := True.
Record MBSBroadcastConfiguration_r17_IEs__Type : Set :=
  make__MBSBroadcastConfiguration_r17_IEs__Type {
    MBSBroadcastConfiguration_r17_IEs__mbs_SessionInfoList_r17 : option MBS_SessionInfoList_r17__Type ;
    MBSBroadcastConfiguration_r17_IEs__mbs_NeighbourCellList_r17 : option MBS_NeighbourCellList_r17__Type ;
    MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17 : option MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__Type ;
    MBSBroadcastConfiguration_r17_IEs__pdsch_ConfigMTCH_r17 : option PDSCH_ConfigBroadcast_r17__Type ;
    MBSBroadcastConfiguration_r17_IEs__mtch_SSB_MappingWindowList_r17 : option MTCH_SSB_MappingWindowList_r17__Type ;
    MBSBroadcastConfiguration_r17_IEs__lateNonCriticalExtension : option octet_string ;
    MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension : option MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type ;
}.
Definition MBSBroadcastConfiguration_r17_IEs__list := (
 Opt MBS_SessionInfoList_r17__Type MBS_SessionInfoList_r17__cond ::
 Opt MBS_NeighbourCellList_r17__Type MBS_NeighbourCellList_r17__cond ::
 Opt MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__Type MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__cond ::
 Opt PDSCH_ConfigBroadcast_r17__Type PDSCH_ConfigBroadcast_r17__cond ::
 Opt MTCH_SSB_MappingWindowList_r17__Type MTCH_SSB_MappingWindowList_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__cond ::
 nil).
Definition MBSBroadcastConfiguration_r17_IEs__cond z := 
  opt_cond MBS_SessionInfoList_r17__cond (MBSBroadcastConfiguration_r17_IEs__mbs_SessionInfoList_r17 z) /\
  opt_cond MBS_NeighbourCellList_r17__cond (MBSBroadcastConfiguration_r17_IEs__mbs_NeighbourCellList_r17 z) /\
  opt_cond MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__cond (MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17 z) /\
  opt_cond PDSCH_ConfigBroadcast_r17__cond (MBSBroadcastConfiguration_r17_IEs__pdsch_ConfigMTCH_r17 z) /\
  opt_cond MTCH_SSB_MappingWindowList_r17__cond (MBSBroadcastConfiguration_r17_IEs__mtch_SSB_MappingWindowList_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MBSBroadcastConfiguration_r17_IEs__lateNonCriticalExtension z) /\
  opt_cond MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__cond (MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension z) /\
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
Definition MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__Format : T_Format MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__Type MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__cond := seq_of_format DRX_ConfigPTM_r17__Format 1 maxNrofDRX_ConfigPTM_r17 MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__helper1 MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__helper2.

Opaque MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__cond MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__Format.

Definition MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__helper : forall a : MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type, True -> True /\ make__MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Format : T_Format MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Type)
    MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__cond MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Format.


Definition MBSBroadcastConfiguration_r17_IEs__Format_Type := Eval cbn in seq_format_prod MBSBroadcastConfiguration_r17_IEs__list.
Definition MBSBroadcastConfiguration_r17_IEs__Format_list : MBSBroadcastConfiguration_r17_IEs__Format_Type :=
  (MBS_SessionInfoList_r17__Format, (MBS_NeighbourCellList_r17__Format, (MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17__Format, (PDSCH_ConfigBroadcast_r17__Format, (MTCH_SSB_MappingWindowList_r17__Format, (octet_string_nc__Format, (MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension__Format, unit_format))))))).
Definition MBSBroadcastConfiguration_r17_IEs__list__Format := (*Eval compute in *) seq_format MBSBroadcastConfiguration_r17_IEs__list MBSBroadcastConfiguration_r17_IEs__Format_list.
Definition MBSBroadcastConfiguration_r17_IEs__F1 z :=
  (MBSBroadcastConfiguration_r17_IEs__mbs_SessionInfoList_r17 z, (MBSBroadcastConfiguration_r17_IEs__mbs_NeighbourCellList_r17 z, (MBSBroadcastConfiguration_r17_IEs__drx_ConfigPTM_List_r17 z, (MBSBroadcastConfiguration_r17_IEs__pdsch_ConfigMTCH_r17 z, (MBSBroadcastConfiguration_r17_IEs__mtch_SSB_MappingWindowList_r17 z, (MBSBroadcastConfiguration_r17_IEs__lateNonCriticalExtension z, (MBSBroadcastConfiguration_r17_IEs__nonCriticalExtension z, tt))))))).
Definition MBSBroadcastConfiguration_r17_IEs__F2 (y : seq_type MBSBroadcastConfiguration_r17_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__MBSBroadcastConfiguration_r17_IEs__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma MBSBroadcastConfiguration_r17_IEs__F1F2_cond (z : MBSBroadcastConfiguration_r17_IEs__Type)
  : MBSBroadcastConfiguration_r17_IEs__cond z ->
  (seq_cond MBSBroadcastConfiguration_r17_IEs__list (MBSBroadcastConfiguration_r17_IEs__F1 z)).
intro H. unfold MBSBroadcastConfiguration_r17_IEs__cond in H. simpl. auto. Qed.
Lemma MBSBroadcastConfiguration_r17_IEs__F1F2_cond2 (z : MBSBroadcastConfiguration_r17_IEs__Type)
 : MBSBroadcastConfiguration_r17_IEs__F2 (MBSBroadcastConfiguration_r17_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MBSBroadcastConfiguration_r17_IEs__F2F1_cond (y : seq_type MBSBroadcastConfiguration_r17_IEs__list)
  : seq_cond MBSBroadcastConfiguration_r17_IEs__list y ->
 (MBSBroadcastConfiguration_r17_IEs__cond (MBSBroadcastConfiguration_r17_IEs__F2 y)) /\  MBSBroadcastConfiguration_r17_IEs__F1 (MBSBroadcastConfiguration_r17_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MBSBroadcastConfiguration_r17_IEs__cond. simpl in *. auto.
 - simpl. unfold MBSBroadcastConfiguration_r17_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MBSBroadcastConfiguration_r17_IEs__Format : T_Format MBSBroadcastConfiguration_r17_IEs__Type MBSBroadcastConfiguration_r17_IEs__cond :=
        proj2_format  MBSBroadcastConfiguration_r17_IEs__cond MBSBroadcastConfiguration_r17_IEs__list__Format
    MBSBroadcastConfiguration_r17_IEs__F1 MBSBroadcastConfiguration_r17_IEs__F2 MBSBroadcastConfiguration_r17_IEs__F1F2_cond  MBSBroadcastConfiguration_r17_IEs__F1F2_cond2 MBSBroadcastConfiguration_r17_IEs__F2F1_cond.
Opaque MBSBroadcastConfiguration_r17_IEs__cond MBSBroadcastConfiguration_r17_IEs__Format.

