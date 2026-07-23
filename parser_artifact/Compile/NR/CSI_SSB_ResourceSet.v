Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_SSB_ResourceSetId.

Opaque CSI_SSB_ResourceSetId__cond CSI_SSB_ResourceSetId__Format.

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Definition CSI_SSB_ResourceSet__csi_SSB_ResourceList__Type := list SSB_Index__Type.

Lemma CSI_SSB_ResourceSet__csi_SSB_ResourceList__helper1 : (0 <= 1 <= maxNrofCSI_SSB_ResourcePerSet)%Z. unfold maxNrofCSI_SSB_ResourcePerSet.
 lia. Qed.
Lemma CSI_SSB_ResourceSet__csi_SSB_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_SSB_ResourcePerSet - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_SSB_ResourcePerSet - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_SSB_ResourceSet__csi_SSB_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_SSB_ResourceSet__csi_SSB_ResourceList__cond (z : CSI_SSB_ResourceSet__csi_SSB_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_SSB_ResourcePerSet)%Z /\ (list_and SSB_Index__cond z) .

Require Import NR.ServingAdditionalPCIIndex_r17.

Opaque ServingAdditionalPCIIndex_r17__cond ServingAdditionalPCIIndex_r17__Format.

Definition CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__Type := list ServingAdditionalPCIIndex_r17__Type.

Lemma CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__helper1 : (0 <= 1 <= maxNrofCSI_SSB_ResourcePerSet)%Z. unfold maxNrofCSI_SSB_ResourcePerSet.
 lia. Qed.
Lemma CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_SSB_ResourcePerSet - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_SSB_ResourcePerSet - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__cond (z : CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_SSB_ResourcePerSet)%Z /\ (list_and ServingAdditionalPCIIndex_r17__cond z) .

Record CSI_SSB_ResourceSet__ext0O__Type : Set :=
  make__CSI_SSB_ResourceSet__ext0O__Type {
    CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17 : option CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__Type ;
}.
Definition CSI_SSB_ResourceSet__ext0O__list := (
 Opt CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__Type CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__cond ::
 nil).
Definition CSI_SSB_ResourceSet__ext0O__cond z := 
  opt_cond CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__cond (CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17 z) /\
  True.

Definition CSI_SSB_ResourceSet__ext0__Type := CSI_SSB_ResourceSet__ext0O__Type.
Definition CSI_SSB_ResourceSet__ext0__cond := CSI_SSB_ResourceSet__ext0O__cond.

Record CSI_SSB_ResourceSet__Type : Set :=
  make__CSI_SSB_ResourceSet__Type {
    CSI_SSB_ResourceSet__csi_SSB_ResourceSetId : CSI_SSB_ResourceSetId__Type ;
    CSI_SSB_ResourceSet__csi_SSB_ResourceList : CSI_SSB_ResourceSet__csi_SSB_ResourceList__Type ;
    CSI_SSB_ResourceSet__ext0 : option CSI_SSB_ResourceSet__ext0__Type ;
}.
Definition CSI_SSB_ResourceSet__root_list : list seq_elem := (
 Nor CSI_SSB_ResourceSetId__Type CSI_SSB_ResourceSetId__cond ::
 Nor CSI_SSB_ResourceSet__csi_SSB_ResourceList__Type CSI_SSB_ResourceSet__csi_SSB_ResourceList__cond ::
 nil).
Definition CSI_SSB_ResourceSet__ext_list : list typ := (
  typ_cons CSI_SSB_ResourceSet__ext0__Type CSI_SSB_ResourceSet__ext0__cond ::
  nil).
Definition CSI_SSB_ResourceSet__cond (z : CSI_SSB_ResourceSet__Type) := 
(  CSI_SSB_ResourceSetId__cond (CSI_SSB_ResourceSet__csi_SSB_ResourceSetId z) /\
  CSI_SSB_ResourceSet__csi_SSB_ResourceList__cond (CSI_SSB_ResourceSet__csi_SSB_ResourceList z) /\
  True) /\ 
(  opt_cond CSI_SSB_ResourceSet__ext0__cond (CSI_SSB_ResourceSet__ext0 z) /\
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
Definition CSI_SSB_ResourceSet__csi_SSB_ResourceList__Format : T_Format CSI_SSB_ResourceSet__csi_SSB_ResourceList__Type CSI_SSB_ResourceSet__csi_SSB_ResourceList__cond := seq_of_format SSB_Index__Format 1 maxNrofCSI_SSB_ResourcePerSet CSI_SSB_ResourceSet__csi_SSB_ResourceList__helper1 CSI_SSB_ResourceSet__csi_SSB_ResourceList__helper2.

Opaque CSI_SSB_ResourceSet__csi_SSB_ResourceList__cond CSI_SSB_ResourceSet__csi_SSB_ResourceList__Format.

Definition CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__Format : T_Format CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__Type CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__cond := seq_of_format ServingAdditionalPCIIndex_r17__Format 1 maxNrofCSI_SSB_ResourcePerSet CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__helper1 CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__helper2.

Opaque CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__cond CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__Format.


Definition CSI_SSB_ResourceSet__ext0O__Format_Type := Eval cbn in seq_format_prod CSI_SSB_ResourceSet__ext0O__list.
Definition CSI_SSB_ResourceSet__ext0O__Format_list : CSI_SSB_ResourceSet__ext0O__Format_Type :=
  (CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17__Format, unit_format).
Definition CSI_SSB_ResourceSet__ext0O__list__Format := (*Eval compute in *) seq_format CSI_SSB_ResourceSet__ext0O__list CSI_SSB_ResourceSet__ext0O__Format_list.
Definition CSI_SSB_ResourceSet__ext0O__F1 z :=
  (CSI_SSB_ResourceSet__ext0O__servingAdditionalPCIList_r17 z, tt).
Definition CSI_SSB_ResourceSet__ext0O__F2 (y : seq_type CSI_SSB_ResourceSet__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CSI_SSB_ResourceSet__ext0O__Type i0
  end.
Lemma CSI_SSB_ResourceSet__ext0O__F1F2_cond (z : CSI_SSB_ResourceSet__ext0O__Type)
  : CSI_SSB_ResourceSet__ext0O__cond z ->
  (seq_cond CSI_SSB_ResourceSet__ext0O__list (CSI_SSB_ResourceSet__ext0O__F1 z)).
intro H. unfold CSI_SSB_ResourceSet__ext0O__cond in H. simpl. auto. Qed.
Lemma CSI_SSB_ResourceSet__ext0O__F1F2_cond2 (z : CSI_SSB_ResourceSet__ext0O__Type)
 : CSI_SSB_ResourceSet__ext0O__F2 (CSI_SSB_ResourceSet__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_SSB_ResourceSet__ext0O__F2F1_cond (y : seq_type CSI_SSB_ResourceSet__ext0O__list)
  : seq_cond CSI_SSB_ResourceSet__ext0O__list y ->
 (CSI_SSB_ResourceSet__ext0O__cond (CSI_SSB_ResourceSet__ext0O__F2 y)) /\  CSI_SSB_ResourceSet__ext0O__F1 (CSI_SSB_ResourceSet__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_SSB_ResourceSet__ext0O__cond. simpl in *. auto.
 - simpl. unfold CSI_SSB_ResourceSet__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_SSB_ResourceSet__ext0O__Format : T_Format CSI_SSB_ResourceSet__ext0O__Type CSI_SSB_ResourceSet__ext0O__cond :=
        proj2_format  CSI_SSB_ResourceSet__ext0O__cond CSI_SSB_ResourceSet__ext0O__list__Format
    CSI_SSB_ResourceSet__ext0O__F1 CSI_SSB_ResourceSet__ext0O__F2 CSI_SSB_ResourceSet__ext0O__F1F2_cond  CSI_SSB_ResourceSet__ext0O__F1F2_cond2 CSI_SSB_ResourceSet__ext0O__F2F1_cond.
Opaque CSI_SSB_ResourceSet__ext0O__cond CSI_SSB_ResourceSet__ext0O__Format.

Definition CSI_SSB_ResourceSet__ext0__check_all_none (b : CSI_SSB_ResourceSet__ext0O__Type) : bool :=
match b with 
  | make__CSI_SSB_ResourceSet__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CSI_SSB_ResourceSet__ext0__Format : T_Format CSI_SSB_ResourceSet__ext0__Type CSI_SSB_ResourceSet__ext0__cond :=
  restrict_add_format CSI_SSB_ResourceSet__ext0__check_all_none CSI_SSB_ResourceSet__ext0O__Format.

Opaque CSI_SSB_ResourceSet__ext0__cond CSI_SSB_ResourceSet__ext0__Format.


Definition CSI_SSB_ResourceSet__root_Format_Type := Eval cbn in seq_format_prod CSI_SSB_ResourceSet__root_list.
Definition CSI_SSB_ResourceSet__root_Format_list : CSI_SSB_ResourceSet__root_Format_Type :=
  (CSI_SSB_ResourceSetId__Format, (CSI_SSB_ResourceSet__csi_SSB_ResourceList__Format, unit_format)).

Definition CSI_SSB_ResourceSet__ext_Format_Type := Eval cbn in get_formats CSI_SSB_ResourceSet__ext_list.
Definition CSI_SSB_ResourceSet__ext_Format_list : CSI_SSB_ResourceSet__ext_Format_Type :=
  (CSI_SSB_ResourceSet__ext0__Format, unit__Format).

Definition CSI_SSB_ResourceSet__list_type : Set := (seq_type CSI_SSB_ResourceSet__root_list) * (seq_ext_type CSI_SSB_ResourceSet__ext_list).
Definition CSI_SSB_ResourceSet__list_cond (z : CSI_SSB_ResourceSet__list_type) : Prop :=
        (seq_cond CSI_SSB_ResourceSet__root_list (fst z)) /\ (seq_ext_cond CSI_SSB_ResourceSet__ext_list (snd z)).
Definition CSI_SSB_ResourceSet__list_format : T_Format CSI_SSB_ResourceSet__list_type CSI_SSB_ResourceSet__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_SSB_ResourceSet__root_list CSI_SSB_ResourceSet__root_Format_list CSI_SSB_ResourceSet__ext_list CSI_SSB_ResourceSet__ext_Format_list.

Opaque CSI_SSB_ResourceSet__list_format.
Definition CSI_SSB_ResourceSet__F1 (z : CSI_SSB_ResourceSet__Type) : CSI_SSB_ResourceSet__list_type :=
  (((CSI_SSB_ResourceSet__csi_SSB_ResourceSetId z, (CSI_SSB_ResourceSet__csi_SSB_ResourceList z, tt))), (
(CSI_SSB_ResourceSet__ext0 z, tt))).
Definition CSI_SSB_ResourceSet__F2 (y : CSI_SSB_ResourceSet__list_type) : CSI_SSB_ResourceSet__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__CSI_SSB_ResourceSet__Type j0 j1 i0
  end.
Definition CSI_SSB_ResourceSet__helper1 : (forall a : CSI_SSB_ResourceSet__Type, CSI_SSB_ResourceSet__cond a -> CSI_SSB_ResourceSet__list_cond (CSI_SSB_ResourceSet__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_SSB_ResourceSet__helper2 : (forall a : CSI_SSB_ResourceSet__Type, CSI_SSB_ResourceSet__F2 (CSI_SSB_ResourceSet__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_SSB_ResourceSet__helper3 : (forall b : CSI_SSB_ResourceSet__list_type, CSI_SSB_ResourceSet__list_cond b -> CSI_SSB_ResourceSet__cond (CSI_SSB_ResourceSet__F2 b) /\ CSI_SSB_ResourceSet__F1 (CSI_SSB_ResourceSet__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_SSB_ResourceSet__cond, CSI_SSB_ResourceSet__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_SSB_ResourceSet__Format : T_Format CSI_SSB_ResourceSet__Type CSI_SSB_ResourceSet__cond :=
 proj2_format CSI_SSB_ResourceSet__cond CSI_SSB_ResourceSet__list_format  CSI_SSB_ResourceSet__F1 CSI_SSB_ResourceSet__F2 CSI_SSB_ResourceSet__helper1 CSI_SSB_ResourceSet__helper2 CSI_SSB_ResourceSet__helper3.

Opaque CSI_SSB_ResourceSet__cond CSI_SSB_ResourceSet__Format.

