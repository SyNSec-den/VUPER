Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_IM_ResourceSetId.

Opaque CSI_IM_ResourceSetId__cond CSI_IM_ResourceSetId__Format.

Require Import NR.CSI_IM_ResourceId.

Opaque CSI_IM_ResourceId__cond CSI_IM_ResourceId__Format.

Definition CSI_IM_ResourceSet__csi_IM_Resources__Type := list CSI_IM_ResourceId__Type.

Lemma CSI_IM_ResourceSet__csi_IM_Resources__helper1 : (0 <= 1 <= maxNrofCSI_IM_ResourcesPerSet)%Z. unfold maxNrofCSI_IM_ResourcesPerSet.
 lia. Qed.
Lemma CSI_IM_ResourceSet__csi_IM_Resources__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_IM_ResourcesPerSet - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_IM_ResourcesPerSet - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_IM_ResourceSet__csi_IM_Resources__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_IM_ResourceSet__csi_IM_Resources__cond (z : CSI_IM_ResourceSet__csi_IM_Resources__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_IM_ResourcesPerSet)%Z /\ (list_and CSI_IM_ResourceId__cond z) .

Record CSI_IM_ResourceSet__Type : Set :=
  make__CSI_IM_ResourceSet__Type {
    CSI_IM_ResourceSet__csi_IM_ResourceSetId : CSI_IM_ResourceSetId__Type ;
    CSI_IM_ResourceSet__csi_IM_Resources : CSI_IM_ResourceSet__csi_IM_Resources__Type ;
}.
Definition CSI_IM_ResourceSet__root_list : list seq_elem := (
 Nor CSI_IM_ResourceSetId__Type CSI_IM_ResourceSetId__cond ::
 Nor CSI_IM_ResourceSet__csi_IM_Resources__Type CSI_IM_ResourceSet__csi_IM_Resources__cond ::
 nil).
Definition CSI_IM_ResourceSet__ext_list : list typ := (
  nil).
Definition CSI_IM_ResourceSet__cond (z : CSI_IM_ResourceSet__Type) := 
(  CSI_IM_ResourceSetId__cond (CSI_IM_ResourceSet__csi_IM_ResourceSetId z) /\
  CSI_IM_ResourceSet__csi_IM_Resources__cond (CSI_IM_ResourceSet__csi_IM_Resources z) /\
  True) /\ 
(  True).


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
Definition CSI_IM_ResourceSet__csi_IM_Resources__Format : T_Format CSI_IM_ResourceSet__csi_IM_Resources__Type CSI_IM_ResourceSet__csi_IM_Resources__cond := seq_of_format CSI_IM_ResourceId__Format 1 maxNrofCSI_IM_ResourcesPerSet CSI_IM_ResourceSet__csi_IM_Resources__helper1 CSI_IM_ResourceSet__csi_IM_Resources__helper2.

Opaque CSI_IM_ResourceSet__csi_IM_Resources__cond CSI_IM_ResourceSet__csi_IM_Resources__Format.


Definition CSI_IM_ResourceSet__root_Format_Type := Eval cbn in seq_format_prod CSI_IM_ResourceSet__root_list.
Definition CSI_IM_ResourceSet__root_Format_list : CSI_IM_ResourceSet__root_Format_Type :=
  (CSI_IM_ResourceSetId__Format, (CSI_IM_ResourceSet__csi_IM_Resources__Format, unit_format)).

Definition CSI_IM_ResourceSet__ext_Format_Type := Eval cbn in get_formats CSI_IM_ResourceSet__ext_list.
Definition CSI_IM_ResourceSet__ext_Format_list : CSI_IM_ResourceSet__ext_Format_Type :=
  unit__Format.

Definition CSI_IM_ResourceSet__list_type : Set := (seq_type CSI_IM_ResourceSet__root_list) * (seq_ext_type CSI_IM_ResourceSet__ext_list).
Definition CSI_IM_ResourceSet__list_cond (z : CSI_IM_ResourceSet__list_type) : Prop :=
        (seq_cond CSI_IM_ResourceSet__root_list (fst z)) /\ (seq_ext_cond CSI_IM_ResourceSet__ext_list (snd z)).
Definition CSI_IM_ResourceSet__list_format : T_Format CSI_IM_ResourceSet__list_type CSI_IM_ResourceSet__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_IM_ResourceSet__root_list CSI_IM_ResourceSet__root_Format_list CSI_IM_ResourceSet__ext_list CSI_IM_ResourceSet__ext_Format_list.

Opaque CSI_IM_ResourceSet__list_format.
Definition CSI_IM_ResourceSet__F1 (z : CSI_IM_ResourceSet__Type) : CSI_IM_ResourceSet__list_type :=
  (((CSI_IM_ResourceSet__csi_IM_ResourceSetId z, (CSI_IM_ResourceSet__csi_IM_Resources z, tt))), (
tt)).
Definition CSI_IM_ResourceSet__F2 (y : CSI_IM_ResourceSet__list_type) : CSI_IM_ResourceSet__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__CSI_IM_ResourceSet__Type j0 j1
  end.
Definition CSI_IM_ResourceSet__helper1 : (forall a : CSI_IM_ResourceSet__Type, CSI_IM_ResourceSet__cond a -> CSI_IM_ResourceSet__list_cond (CSI_IM_ResourceSet__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_IM_ResourceSet__helper2 : (forall a : CSI_IM_ResourceSet__Type, CSI_IM_ResourceSet__F2 (CSI_IM_ResourceSet__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_IM_ResourceSet__helper3 : (forall b : CSI_IM_ResourceSet__list_type, CSI_IM_ResourceSet__list_cond b -> CSI_IM_ResourceSet__cond (CSI_IM_ResourceSet__F2 b) /\ CSI_IM_ResourceSet__F1 (CSI_IM_ResourceSet__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_IM_ResourceSet__cond, CSI_IM_ResourceSet__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_IM_ResourceSet__Format : T_Format CSI_IM_ResourceSet__Type CSI_IM_ResourceSet__cond :=
 proj2_format CSI_IM_ResourceSet__cond CSI_IM_ResourceSet__list_format  CSI_IM_ResourceSet__F1 CSI_IM_ResourceSet__F2 CSI_IM_ResourceSet__helper1 CSI_IM_ResourceSet__helper2 CSI_IM_ResourceSet__helper3.

Opaque CSI_IM_ResourceSet__cond CSI_IM_ResourceSet__Format.

