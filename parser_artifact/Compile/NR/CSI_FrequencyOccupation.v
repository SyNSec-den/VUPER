Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CSI_FrequencyOccupation__startingRB__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma CSI_FrequencyOccupation__startingRB__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_FrequencyOccupation__startingRB__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_FrequencyOccupation__startingRB__Type := Z.
Definition CSI_FrequencyOccupation__startingRB__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Lemma CSI_FrequencyOccupation__nrofRBs__helper1 : (24 <= maxNrofPhysicalResourceBlocksPlus1)%Z. unfold maxNrofPhysicalResourceBlocksPlus1.
 lia. Qed.
Lemma CSI_FrequencyOccupation__nrofRBs__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocksPlus1 - 24)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocksPlus1 - 24))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_FrequencyOccupation__nrofRBs__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_FrequencyOccupation__nrofRBs__Type := Z.
Definition CSI_FrequencyOccupation__nrofRBs__cond := (fun z => (24 <= z <= maxNrofPhysicalResourceBlocksPlus1)%Z).
Record CSI_FrequencyOccupation__Type : Set :=
  make__CSI_FrequencyOccupation__Type {
    CSI_FrequencyOccupation__startingRB : Z ;
    CSI_FrequencyOccupation__nrofRBs : Z ;
}.
Definition CSI_FrequencyOccupation__root_list : list seq_elem := (
 Nor Z CSI_FrequencyOccupation__startingRB__cond ::
 Nor Z CSI_FrequencyOccupation__nrofRBs__cond ::
 nil).
Definition CSI_FrequencyOccupation__ext_list : list typ := (
  nil).
Definition CSI_FrequencyOccupation__cond (z : CSI_FrequencyOccupation__Type) := 
(  CSI_FrequencyOccupation__startingRB__cond (CSI_FrequencyOccupation__startingRB z) /\
  CSI_FrequencyOccupation__nrofRBs__cond (CSI_FrequencyOccupation__nrofRBs z) /\
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
Definition CSI_FrequencyOccupation__startingRB__Format : T_Format Z CSI_FrequencyOccupation__startingRB__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) CSI_FrequencyOccupation__startingRB__helper1 CSI_FrequencyOccupation__startingRB__helper2.

Opaque CSI_FrequencyOccupation__startingRB__cond CSI_FrequencyOccupation__startingRB__Format.

Definition CSI_FrequencyOccupation__nrofRBs__Format : T_Format Z CSI_FrequencyOccupation__nrofRBs__cond :=
 ranged_int_format (24) (maxNrofPhysicalResourceBlocksPlus1) CSI_FrequencyOccupation__nrofRBs__helper1 CSI_FrequencyOccupation__nrofRBs__helper2.

Opaque CSI_FrequencyOccupation__nrofRBs__cond CSI_FrequencyOccupation__nrofRBs__Format.


Definition CSI_FrequencyOccupation__root_Format_Type := Eval cbn in seq_format_prod CSI_FrequencyOccupation__root_list.
Definition CSI_FrequencyOccupation__root_Format_list : CSI_FrequencyOccupation__root_Format_Type :=
  (CSI_FrequencyOccupation__startingRB__Format, (CSI_FrequencyOccupation__nrofRBs__Format, unit_format)).

Definition CSI_FrequencyOccupation__ext_Format_Type := Eval cbn in get_formats CSI_FrequencyOccupation__ext_list.
Definition CSI_FrequencyOccupation__ext_Format_list : CSI_FrequencyOccupation__ext_Format_Type :=
  unit__Format.

Definition CSI_FrequencyOccupation__list_type : Set := (seq_type CSI_FrequencyOccupation__root_list) * (seq_ext_type CSI_FrequencyOccupation__ext_list).
Definition CSI_FrequencyOccupation__list_cond (z : CSI_FrequencyOccupation__list_type) : Prop :=
        (seq_cond CSI_FrequencyOccupation__root_list (fst z)) /\ (seq_ext_cond CSI_FrequencyOccupation__ext_list (snd z)).
Definition CSI_FrequencyOccupation__list_format : T_Format CSI_FrequencyOccupation__list_type CSI_FrequencyOccupation__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_FrequencyOccupation__root_list CSI_FrequencyOccupation__root_Format_list CSI_FrequencyOccupation__ext_list CSI_FrequencyOccupation__ext_Format_list.

Opaque CSI_FrequencyOccupation__list_format.
Definition CSI_FrequencyOccupation__F1 (z : CSI_FrequencyOccupation__Type) : CSI_FrequencyOccupation__list_type :=
  (((CSI_FrequencyOccupation__startingRB z, (CSI_FrequencyOccupation__nrofRBs z, tt))), (
tt)).
Definition CSI_FrequencyOccupation__F2 (y : CSI_FrequencyOccupation__list_type) : CSI_FrequencyOccupation__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__CSI_FrequencyOccupation__Type j0 j1
  end.
Definition CSI_FrequencyOccupation__helper1 : (forall a : CSI_FrequencyOccupation__Type, CSI_FrequencyOccupation__cond a -> CSI_FrequencyOccupation__list_cond (CSI_FrequencyOccupation__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_FrequencyOccupation__helper2 : (forall a : CSI_FrequencyOccupation__Type, CSI_FrequencyOccupation__F2 (CSI_FrequencyOccupation__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_FrequencyOccupation__helper3 : (forall b : CSI_FrequencyOccupation__list_type, CSI_FrequencyOccupation__list_cond b -> CSI_FrequencyOccupation__cond (CSI_FrequencyOccupation__F2 b) /\ CSI_FrequencyOccupation__F1 (CSI_FrequencyOccupation__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_FrequencyOccupation__cond, CSI_FrequencyOccupation__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_FrequencyOccupation__Format : T_Format CSI_FrequencyOccupation__Type CSI_FrequencyOccupation__cond :=
 proj2_format CSI_FrequencyOccupation__cond CSI_FrequencyOccupation__list_format  CSI_FrequencyOccupation__F1 CSI_FrequencyOccupation__F2 CSI_FrequencyOccupation__helper1 CSI_FrequencyOccupation__helper2 CSI_FrequencyOccupation__helper3.

Opaque CSI_FrequencyOccupation__cond CSI_FrequencyOccupation__Format.

