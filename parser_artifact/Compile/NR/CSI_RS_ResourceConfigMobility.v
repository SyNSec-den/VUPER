Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.CSI_RS_CellMobility.

Opaque CSI_RS_CellMobility__cond CSI_RS_CellMobility__Format.

Definition CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__Type := list CSI_RS_CellMobility__Type.

Lemma CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__helper1 : (0 <= 1 <= maxNrofCSI_RS_CellsRRM)%Z. unfold maxNrofCSI_RS_CellsRRM.
 lia. Qed.
Lemma CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_CellsRRM - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_CellsRRM - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__cond (z : CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_CellsRRM)%Z /\ (list_and CSI_RS_CellMobility__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Record CSI_RS_ResourceConfigMobility__ext0O__Type : Set :=
  make__CSI_RS_ResourceConfigMobility__ext0O__Type {
    CSI_RS_ResourceConfigMobility__ext0O__refServCellIndex : option ServCellIndex__Type ;
}.
Definition CSI_RS_ResourceConfigMobility__ext0O__list := (
 Opt ServCellIndex__Type ServCellIndex__cond ::
 nil).
Definition CSI_RS_ResourceConfigMobility__ext0O__cond z := 
  opt_cond ServCellIndex__cond (CSI_RS_ResourceConfigMobility__ext0O__refServCellIndex z) /\
  True.

Definition CSI_RS_ResourceConfigMobility__ext0__Type := CSI_RS_ResourceConfigMobility__ext0O__Type.
Definition CSI_RS_ResourceConfigMobility__ext0__cond := CSI_RS_ResourceConfigMobility__ext0O__cond.

Record CSI_RS_ResourceConfigMobility__Type : Set :=
  make__CSI_RS_ResourceConfigMobility__Type {
    CSI_RS_ResourceConfigMobility__subcarrierSpacing : SubcarrierSpacing__Type ;
    CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility : CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__Type ;
    CSI_RS_ResourceConfigMobility__ext0 : option CSI_RS_ResourceConfigMobility__ext0__Type ;
}.
Definition CSI_RS_ResourceConfigMobility__root_list : list seq_elem := (
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__Type CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__cond ::
 nil).
Definition CSI_RS_ResourceConfigMobility__ext_list : list typ := (
  typ_cons CSI_RS_ResourceConfigMobility__ext0__Type CSI_RS_ResourceConfigMobility__ext0__cond ::
  nil).
Definition CSI_RS_ResourceConfigMobility__cond (z : CSI_RS_ResourceConfigMobility__Type) := 
(  SubcarrierSpacing__cond (CSI_RS_ResourceConfigMobility__subcarrierSpacing z) /\
  CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__cond (CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility z) /\
  True) /\ 
(  opt_cond CSI_RS_ResourceConfigMobility__ext0__cond (CSI_RS_ResourceConfigMobility__ext0 z) /\
  True).


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
Definition CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__Format : T_Format CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__Type CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__cond := seq_of_format CSI_RS_CellMobility__Format 1 maxNrofCSI_RS_CellsRRM CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__helper1 CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__helper2.

Opaque CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__cond CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__Format.


Definition CSI_RS_ResourceConfigMobility__ext0O__Format_Type := Eval cbn in seq_format_prod CSI_RS_ResourceConfigMobility__ext0O__list.
Definition CSI_RS_ResourceConfigMobility__ext0O__Format_list : CSI_RS_ResourceConfigMobility__ext0O__Format_Type :=
  (ServCellIndex__Format, unit_format).
Definition CSI_RS_ResourceConfigMobility__ext0O__list__Format := (*Eval compute in *) seq_format CSI_RS_ResourceConfigMobility__ext0O__list CSI_RS_ResourceConfigMobility__ext0O__Format_list.
Definition CSI_RS_ResourceConfigMobility__ext0O__F1 z :=
  (CSI_RS_ResourceConfigMobility__ext0O__refServCellIndex z, tt).
Definition CSI_RS_ResourceConfigMobility__ext0O__F2 (y : seq_type CSI_RS_ResourceConfigMobility__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CSI_RS_ResourceConfigMobility__ext0O__Type i0
  end.
Lemma CSI_RS_ResourceConfigMobility__ext0O__F1F2_cond (z : CSI_RS_ResourceConfigMobility__ext0O__Type)
  : CSI_RS_ResourceConfigMobility__ext0O__cond z ->
  (seq_cond CSI_RS_ResourceConfigMobility__ext0O__list (CSI_RS_ResourceConfigMobility__ext0O__F1 z)).
intro H. unfold CSI_RS_ResourceConfigMobility__ext0O__cond in H. simpl. auto. Qed.
Lemma CSI_RS_ResourceConfigMobility__ext0O__F1F2_cond2 (z : CSI_RS_ResourceConfigMobility__ext0O__Type)
 : CSI_RS_ResourceConfigMobility__ext0O__F2 (CSI_RS_ResourceConfigMobility__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_RS_ResourceConfigMobility__ext0O__F2F1_cond (y : seq_type CSI_RS_ResourceConfigMobility__ext0O__list)
  : seq_cond CSI_RS_ResourceConfigMobility__ext0O__list y ->
 (CSI_RS_ResourceConfigMobility__ext0O__cond (CSI_RS_ResourceConfigMobility__ext0O__F2 y)) /\  CSI_RS_ResourceConfigMobility__ext0O__F1 (CSI_RS_ResourceConfigMobility__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_RS_ResourceConfigMobility__ext0O__cond. simpl in *. auto.
 - simpl. unfold CSI_RS_ResourceConfigMobility__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_RS_ResourceConfigMobility__ext0O__Format : T_Format CSI_RS_ResourceConfigMobility__ext0O__Type CSI_RS_ResourceConfigMobility__ext0O__cond :=
        proj2_format  CSI_RS_ResourceConfigMobility__ext0O__cond CSI_RS_ResourceConfigMobility__ext0O__list__Format
    CSI_RS_ResourceConfigMobility__ext0O__F1 CSI_RS_ResourceConfigMobility__ext0O__F2 CSI_RS_ResourceConfigMobility__ext0O__F1F2_cond  CSI_RS_ResourceConfigMobility__ext0O__F1F2_cond2 CSI_RS_ResourceConfigMobility__ext0O__F2F1_cond.
Opaque CSI_RS_ResourceConfigMobility__ext0O__cond CSI_RS_ResourceConfigMobility__ext0O__Format.

Definition CSI_RS_ResourceConfigMobility__ext0__check_all_none (b : CSI_RS_ResourceConfigMobility__ext0O__Type) : bool :=
match b with 
  | make__CSI_RS_ResourceConfigMobility__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CSI_RS_ResourceConfigMobility__ext0__Format : T_Format CSI_RS_ResourceConfigMobility__ext0__Type CSI_RS_ResourceConfigMobility__ext0__cond :=
  restrict_add_format CSI_RS_ResourceConfigMobility__ext0__check_all_none CSI_RS_ResourceConfigMobility__ext0O__Format.

Opaque CSI_RS_ResourceConfigMobility__ext0__cond CSI_RS_ResourceConfigMobility__ext0__Format.


Definition CSI_RS_ResourceConfigMobility__root_Format_Type := Eval cbn in seq_format_prod CSI_RS_ResourceConfigMobility__root_list.
Definition CSI_RS_ResourceConfigMobility__root_Format_list : CSI_RS_ResourceConfigMobility__root_Format_Type :=
  (SubcarrierSpacing__Format, (CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility__Format, unit_format)).

Definition CSI_RS_ResourceConfigMobility__ext_Format_Type := Eval cbn in get_formats CSI_RS_ResourceConfigMobility__ext_list.
Definition CSI_RS_ResourceConfigMobility__ext_Format_list : CSI_RS_ResourceConfigMobility__ext_Format_Type :=
  (CSI_RS_ResourceConfigMobility__ext0__Format, unit__Format).

Definition CSI_RS_ResourceConfigMobility__list_type : Set := (seq_type CSI_RS_ResourceConfigMobility__root_list) * (seq_ext_type CSI_RS_ResourceConfigMobility__ext_list).
Definition CSI_RS_ResourceConfigMobility__list_cond (z : CSI_RS_ResourceConfigMobility__list_type) : Prop :=
        (seq_cond CSI_RS_ResourceConfigMobility__root_list (fst z)) /\ (seq_ext_cond CSI_RS_ResourceConfigMobility__ext_list (snd z)).
Definition CSI_RS_ResourceConfigMobility__list_format : T_Format CSI_RS_ResourceConfigMobility__list_type CSI_RS_ResourceConfigMobility__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_RS_ResourceConfigMobility__root_list CSI_RS_ResourceConfigMobility__root_Format_list CSI_RS_ResourceConfigMobility__ext_list CSI_RS_ResourceConfigMobility__ext_Format_list.

Opaque CSI_RS_ResourceConfigMobility__list_format.
Definition CSI_RS_ResourceConfigMobility__F1 (z : CSI_RS_ResourceConfigMobility__Type) : CSI_RS_ResourceConfigMobility__list_type :=
  (((CSI_RS_ResourceConfigMobility__subcarrierSpacing z, (CSI_RS_ResourceConfigMobility__csi_RS_CellList_Mobility z, tt))), (
(CSI_RS_ResourceConfigMobility__ext0 z, tt))).
Definition CSI_RS_ResourceConfigMobility__F2 (y : CSI_RS_ResourceConfigMobility__list_type) : CSI_RS_ResourceConfigMobility__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__CSI_RS_ResourceConfigMobility__Type j0 j1 i0
  end.
Definition CSI_RS_ResourceConfigMobility__helper1 : (forall a : CSI_RS_ResourceConfigMobility__Type, CSI_RS_ResourceConfigMobility__cond a -> CSI_RS_ResourceConfigMobility__list_cond (CSI_RS_ResourceConfigMobility__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_RS_ResourceConfigMobility__helper2 : (forall a : CSI_RS_ResourceConfigMobility__Type, CSI_RS_ResourceConfigMobility__F2 (CSI_RS_ResourceConfigMobility__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_RS_ResourceConfigMobility__helper3 : (forall b : CSI_RS_ResourceConfigMobility__list_type, CSI_RS_ResourceConfigMobility__list_cond b -> CSI_RS_ResourceConfigMobility__cond (CSI_RS_ResourceConfigMobility__F2 b) /\ CSI_RS_ResourceConfigMobility__F1 (CSI_RS_ResourceConfigMobility__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_RS_ResourceConfigMobility__cond, CSI_RS_ResourceConfigMobility__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_RS_ResourceConfigMobility__Format : T_Format CSI_RS_ResourceConfigMobility__Type CSI_RS_ResourceConfigMobility__cond :=
 proj2_format CSI_RS_ResourceConfigMobility__cond CSI_RS_ResourceConfigMobility__list_format  CSI_RS_ResourceConfigMobility__F1 CSI_RS_ResourceConfigMobility__F2 CSI_RS_ResourceConfigMobility__helper1 CSI_RS_ResourceConfigMobility__helper2 CSI_RS_ResourceConfigMobility__helper3.

Opaque CSI_RS_ResourceConfigMobility__cond CSI_RS_ResourceConfigMobility__Format.

