Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__helper1 : (0 <= maxNrOfTxTEG_ID_1_r17)%Z. unfold maxNrOfTxTEG_ID_1_r17.
 lia. Qed.
Lemma UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__helper2 : to_bit_sz (Z.to_nat (maxNrOfTxTEG_ID_1_r17 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrOfTxTEG_ID_1_r17 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__Type := Z.
Definition UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__cond := (fun z => (0 <= z <= maxNrOfTxTEG_ID_1_r17)%Z).
Require Import NR.NR_TimeStamp_r17.

Opaque NR_TimeStamp_r17__cond NR_TimeStamp_r17__Format.

Require Import NR.SRS_PosResourceId_r16.

Opaque SRS_PosResourceId_r16__cond SRS_PosResourceId_r16__Format.

Definition UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type := list SRS_PosResourceId_r16__Type.

Lemma UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__helper1 : (0 <= 1 <= maxNrofSRS_PosResources_r16)%Z. unfold maxNrofSRS_PosResources_r16.
 lia. Qed.
Lemma UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_PosResources_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_PosResources_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__cond (z : UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_PosResources_r16)%Z /\ (list_and SRS_PosResourceId_r16__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Record UE_TxTEG_Association_r17__Type : Set :=
  make__UE_TxTEG_Association_r17__Type {
    UE_TxTEG_Association_r17__ue_TxTEG_ID_r17 : Z ;
    UE_TxTEG_Association_r17__nr_TimeStamp_r17 : NR_TimeStamp_r17__Type ;
    UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17 : UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type ;
    UE_TxTEG_Association_r17__servCellId_r17 : option ServCellIndex__Type ;
}.
Definition UE_TxTEG_Association_r17__list := (
 Nor Z UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__cond ::
 Nor NR_TimeStamp_r17__Type NR_TimeStamp_r17__cond ::
 Nor UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 nil).
Definition UE_TxTEG_Association_r17__cond z := 
  UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__cond (UE_TxTEG_Association_r17__ue_TxTEG_ID_r17 z) /\
  NR_TimeStamp_r17__cond (UE_TxTEG_Association_r17__nr_TimeStamp_r17 z) /\
  UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__cond (UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17 z) /\
  opt_cond ServCellIndex__cond (UE_TxTEG_Association_r17__servCellId_r17 z) /\
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
Definition UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__Format : T_Format Z UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__cond :=
 ranged_int_format (0) (maxNrOfTxTEG_ID_1_r17) UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__helper1 UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__helper2.

Opaque UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__cond UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__Format.

Definition UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Format : T_Format UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Type UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__cond := seq_of_format SRS_PosResourceId_r16__Format 1 maxNrofSRS_PosResources_r16 UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__helper1 UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__helper2.

Opaque UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__cond UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Format.


Definition UE_TxTEG_Association_r17__Format_Type := Eval cbn in seq_format_prod UE_TxTEG_Association_r17__list.
Definition UE_TxTEG_Association_r17__Format_list : UE_TxTEG_Association_r17__Format_Type :=
  (UE_TxTEG_Association_r17__ue_TxTEG_ID_r17__Format, (NR_TimeStamp_r17__Format, (UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17__Format, (ServCellIndex__Format, unit_format)))).
Definition UE_TxTEG_Association_r17__list__Format := (*Eval compute in *) seq_format UE_TxTEG_Association_r17__list UE_TxTEG_Association_r17__Format_list.
Definition UE_TxTEG_Association_r17__F1 z :=
  (UE_TxTEG_Association_r17__ue_TxTEG_ID_r17 z, (UE_TxTEG_Association_r17__nr_TimeStamp_r17 z, (UE_TxTEG_Association_r17__associatedSRS_PosResourceIdList_r17 z, (UE_TxTEG_Association_r17__servCellId_r17 z, tt)))).
Definition UE_TxTEG_Association_r17__F2 (y : seq_type UE_TxTEG_Association_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__UE_TxTEG_Association_r17__Type i0 i1 i2 i3
  end.
Lemma UE_TxTEG_Association_r17__F1F2_cond (z : UE_TxTEG_Association_r17__Type)
  : UE_TxTEG_Association_r17__cond z ->
  (seq_cond UE_TxTEG_Association_r17__list (UE_TxTEG_Association_r17__F1 z)).
intro H. unfold UE_TxTEG_Association_r17__cond in H. simpl. auto. Qed.
Lemma UE_TxTEG_Association_r17__F1F2_cond2 (z : UE_TxTEG_Association_r17__Type)
 : UE_TxTEG_Association_r17__F2 (UE_TxTEG_Association_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_TxTEG_Association_r17__F2F1_cond (y : seq_type UE_TxTEG_Association_r17__list)
  : seq_cond UE_TxTEG_Association_r17__list y ->
 (UE_TxTEG_Association_r17__cond (UE_TxTEG_Association_r17__F2 y)) /\  UE_TxTEG_Association_r17__F1 (UE_TxTEG_Association_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_TxTEG_Association_r17__cond. simpl in *. auto.
 - simpl. unfold UE_TxTEG_Association_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_TxTEG_Association_r17__Format : T_Format UE_TxTEG_Association_r17__Type UE_TxTEG_Association_r17__cond :=
        proj2_format  UE_TxTEG_Association_r17__cond UE_TxTEG_Association_r17__list__Format
    UE_TxTEG_Association_r17__F1 UE_TxTEG_Association_r17__F2 UE_TxTEG_Association_r17__F1F2_cond  UE_TxTEG_Association_r17__F1F2_cond2 UE_TxTEG_Association_r17__F2F1_cond.
Opaque UE_TxTEG_Association_r17__cond UE_TxTEG_Association_r17__Format.

