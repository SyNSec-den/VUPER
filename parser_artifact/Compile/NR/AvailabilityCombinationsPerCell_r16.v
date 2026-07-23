Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.AvailabilityCombinationsPerCellIndex_r16.

Opaque AvailabilityCombinationsPerCellIndex_r16__cond AvailabilityCombinationsPerCellIndex_r16__Format.

Require Import NR.CellIdentity.

Opaque CellIdentity__cond CellIdentity__Format.

Lemma AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__helper1 : (0 <= maxAI_DCI_PayloadSize_1_r16)%Z. unfold maxAI_DCI_PayloadSize_1_r16.
 lia. Qed.
Lemma AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__helper2 : to_bit_sz (Z.to_nat (maxAI_DCI_PayloadSize_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxAI_DCI_PayloadSize_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__Type := Z.
Definition AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__cond := (fun z => (0 <= z <= maxAI_DCI_PayloadSize_1_r16)%Z).
Require Import NR.AvailabilityCombination_r16.

Opaque AvailabilityCombination_r16__cond AvailabilityCombination_r16__Format.

Definition AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__Type := list AvailabilityCombination_r16__Type.

Lemma AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__helper1 : (0 <= 1 <= maxNrofAvailabilityCombinationsPerSet_r16)%Z. unfold maxNrofAvailabilityCombinationsPerSet_r16.
 lia. Qed.
Lemma AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofAvailabilityCombinationsPerSet_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAvailabilityCombinationsPerSet_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__cond (z : AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAvailabilityCombinationsPerSet_r16)%Z /\ (list_and AvailabilityCombination_r16__cond z) .

Require Import NR.AvailabilityCombinationRB_Groups_r17.

Opaque AvailabilityCombinationRB_Groups_r17__cond AvailabilityCombinationRB_Groups_r17__Format.

Definition AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__Type := list AvailabilityCombinationRB_Groups_r17__Type.

Lemma AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__helper1 : (0 <= 1 <= maxNrofAvailabilityCombinationsPerSet_r16)%Z. unfold maxNrofAvailabilityCombinationsPerSet_r16.
 lia. Qed.
Lemma AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofAvailabilityCombinationsPerSet_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAvailabilityCombinationsPerSet_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__cond (z : AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAvailabilityCombinationsPerSet_r16)%Z /\ (list_and AvailabilityCombinationRB_Groups_r17__cond z) .

Record AvailabilityCombinationsPerCell_r16__ext0O__Type : Set :=
  make__AvailabilityCombinationsPerCell_r16__ext0O__Type {
    AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17 : option AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__Type ;
}.
Definition AvailabilityCombinationsPerCell_r16__ext0O__list := (
 Opt AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__Type AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__cond ::
 nil).
Definition AvailabilityCombinationsPerCell_r16__ext0O__cond z := 
  opt_cond AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__cond (AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17 z) /\
  True.

Definition AvailabilityCombinationsPerCell_r16__ext0__Type := AvailabilityCombinationsPerCell_r16__ext0O__Type.
Definition AvailabilityCombinationsPerCell_r16__ext0__cond := AvailabilityCombinationsPerCell_r16__ext0O__cond.

Lemma AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__helper1 : (0 <= maxAI_DCI_PayloadSize_1_r16)%Z. unfold maxAI_DCI_PayloadSize_1_r16.
 lia. Qed.
Lemma AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__helper2 : to_bit_sz (Z.to_nat (maxAI_DCI_PayloadSize_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxAI_DCI_PayloadSize_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__Type := Z.
Definition AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__cond := (fun z => (0 <= z <= maxAI_DCI_PayloadSize_1_r16)%Z).
Record AvailabilityCombinationsPerCell_r16__ext1O__Type : Set :=
  make__AvailabilityCombinationsPerCell_r16__ext1O__Type {
    AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720 : option Z ;
}.
Definition AvailabilityCombinationsPerCell_r16__ext1O__list := (
 Opt Z AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__cond ::
 nil).
Definition AvailabilityCombinationsPerCell_r16__ext1O__cond z := 
  opt_cond AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__cond (AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720 z) /\
  True.

Definition AvailabilityCombinationsPerCell_r16__ext1__Type := AvailabilityCombinationsPerCell_r16__ext1O__Type.
Definition AvailabilityCombinationsPerCell_r16__ext1__cond := AvailabilityCombinationsPerCell_r16__ext1O__cond.

Record AvailabilityCombinationsPerCell_r16__Type : Set :=
  make__AvailabilityCombinationsPerCell_r16__Type {
    AvailabilityCombinationsPerCell_r16__availabilityCombinationsPerCellIndex_r16 : AvailabilityCombinationsPerCellIndex_r16__Type ;
    AvailabilityCombinationsPerCell_r16__iab_DU_CellIdentity_r16 : CellIdentity__Type ;
    AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16 : option Z ;
    AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16 : AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__Type ;
    AvailabilityCombinationsPerCell_r16__ext0 : option AvailabilityCombinationsPerCell_r16__ext0__Type ;
    AvailabilityCombinationsPerCell_r16__ext1 : option AvailabilityCombinationsPerCell_r16__ext1__Type ;
}.
Definition AvailabilityCombinationsPerCell_r16__root_list : list seq_elem := (
 Nor AvailabilityCombinationsPerCellIndex_r16__Type AvailabilityCombinationsPerCellIndex_r16__cond ::
 Nor CellIdentity__Type CellIdentity__cond ::
 Opt Z AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__cond ::
 Nor AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__Type AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__cond ::
 nil).
Definition AvailabilityCombinationsPerCell_r16__ext_list : list typ := (
  typ_cons AvailabilityCombinationsPerCell_r16__ext0__Type AvailabilityCombinationsPerCell_r16__ext0__cond ::
  typ_cons AvailabilityCombinationsPerCell_r16__ext1__Type AvailabilityCombinationsPerCell_r16__ext1__cond ::
  nil).
Definition AvailabilityCombinationsPerCell_r16__cond (z : AvailabilityCombinationsPerCell_r16__Type) := 
(  AvailabilityCombinationsPerCellIndex_r16__cond (AvailabilityCombinationsPerCell_r16__availabilityCombinationsPerCellIndex_r16 z) /\
  CellIdentity__cond (AvailabilityCombinationsPerCell_r16__iab_DU_CellIdentity_r16 z) /\
  opt_cond AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__cond (AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16 z) /\
  AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__cond (AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16 z) /\
  True) /\ 
(  opt_cond AvailabilityCombinationsPerCell_r16__ext0__cond (AvailabilityCombinationsPerCell_r16__ext0 z) /\
  opt_cond AvailabilityCombinationsPerCell_r16__ext1__cond (AvailabilityCombinationsPerCell_r16__ext1 z) /\
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
Definition AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__Format : T_Format Z AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__cond :=
 ranged_int_format (0) (maxAI_DCI_PayloadSize_1_r16) AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__helper1 AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__helper2.

Opaque AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__cond AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__Format.

Definition AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__Format : T_Format AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__Type AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__cond := seq_of_format AvailabilityCombination_r16__Format 1 maxNrofAvailabilityCombinationsPerSet_r16 AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__helper1 AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__helper2.

Opaque AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__cond AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__Format.

Definition AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__Format : T_Format AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__Type AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__cond := seq_of_format AvailabilityCombinationRB_Groups_r17__Format 1 maxNrofAvailabilityCombinationsPerSet_r16 AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__helper1 AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__helper2.

Opaque AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__cond AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__Format.


Definition AvailabilityCombinationsPerCell_r16__ext0O__Format_Type := Eval cbn in seq_format_prod AvailabilityCombinationsPerCell_r16__ext0O__list.
Definition AvailabilityCombinationsPerCell_r16__ext0O__Format_list : AvailabilityCombinationsPerCell_r16__ext0O__Format_Type :=
  (AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17__Format, unit_format).
Definition AvailabilityCombinationsPerCell_r16__ext0O__list__Format := (*Eval compute in *) seq_format AvailabilityCombinationsPerCell_r16__ext0O__list AvailabilityCombinationsPerCell_r16__ext0O__Format_list.
Definition AvailabilityCombinationsPerCell_r16__ext0O__F1 z :=
  (AvailabilityCombinationsPerCell_r16__ext0O__availabilityCombinationsRB_Groups_r17 z, tt).
Definition AvailabilityCombinationsPerCell_r16__ext0O__F2 (y : seq_type AvailabilityCombinationsPerCell_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__AvailabilityCombinationsPerCell_r16__ext0O__Type i0
  end.
Lemma AvailabilityCombinationsPerCell_r16__ext0O__F1F2_cond (z : AvailabilityCombinationsPerCell_r16__ext0O__Type)
  : AvailabilityCombinationsPerCell_r16__ext0O__cond z ->
  (seq_cond AvailabilityCombinationsPerCell_r16__ext0O__list (AvailabilityCombinationsPerCell_r16__ext0O__F1 z)).
intro H. unfold AvailabilityCombinationsPerCell_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma AvailabilityCombinationsPerCell_r16__ext0O__F1F2_cond2 (z : AvailabilityCombinationsPerCell_r16__ext0O__Type)
 : AvailabilityCombinationsPerCell_r16__ext0O__F2 (AvailabilityCombinationsPerCell_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AvailabilityCombinationsPerCell_r16__ext0O__F2F1_cond (y : seq_type AvailabilityCombinationsPerCell_r16__ext0O__list)
  : seq_cond AvailabilityCombinationsPerCell_r16__ext0O__list y ->
 (AvailabilityCombinationsPerCell_r16__ext0O__cond (AvailabilityCombinationsPerCell_r16__ext0O__F2 y)) /\  AvailabilityCombinationsPerCell_r16__ext0O__F1 (AvailabilityCombinationsPerCell_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AvailabilityCombinationsPerCell_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold AvailabilityCombinationsPerCell_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AvailabilityCombinationsPerCell_r16__ext0O__Format : T_Format AvailabilityCombinationsPerCell_r16__ext0O__Type AvailabilityCombinationsPerCell_r16__ext0O__cond :=
        proj2_format  AvailabilityCombinationsPerCell_r16__ext0O__cond AvailabilityCombinationsPerCell_r16__ext0O__list__Format
    AvailabilityCombinationsPerCell_r16__ext0O__F1 AvailabilityCombinationsPerCell_r16__ext0O__F2 AvailabilityCombinationsPerCell_r16__ext0O__F1F2_cond  AvailabilityCombinationsPerCell_r16__ext0O__F1F2_cond2 AvailabilityCombinationsPerCell_r16__ext0O__F2F1_cond.
Opaque AvailabilityCombinationsPerCell_r16__ext0O__cond AvailabilityCombinationsPerCell_r16__ext0O__Format.

Definition AvailabilityCombinationsPerCell_r16__ext0__check_all_none (b : AvailabilityCombinationsPerCell_r16__ext0O__Type) : bool :=
match b with 
  | make__AvailabilityCombinationsPerCell_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition AvailabilityCombinationsPerCell_r16__ext0__Format : T_Format AvailabilityCombinationsPerCell_r16__ext0__Type AvailabilityCombinationsPerCell_r16__ext0__cond :=
  restrict_add_format AvailabilityCombinationsPerCell_r16__ext0__check_all_none AvailabilityCombinationsPerCell_r16__ext0O__Format.

Opaque AvailabilityCombinationsPerCell_r16__ext0__cond AvailabilityCombinationsPerCell_r16__ext0__Format.

Definition AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__Format : T_Format Z AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__cond :=
 ranged_int_format (0) (maxAI_DCI_PayloadSize_1_r16) AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__helper1 AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__helper2.

Opaque AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__cond AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__Format.


Definition AvailabilityCombinationsPerCell_r16__ext1O__Format_Type := Eval cbn in seq_format_prod AvailabilityCombinationsPerCell_r16__ext1O__list.
Definition AvailabilityCombinationsPerCell_r16__ext1O__Format_list : AvailabilityCombinationsPerCell_r16__ext1O__Format_Type :=
  (AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720__Format, unit_format).
Definition AvailabilityCombinationsPerCell_r16__ext1O__list__Format := (*Eval compute in *) seq_format AvailabilityCombinationsPerCell_r16__ext1O__list AvailabilityCombinationsPerCell_r16__ext1O__Format_list.
Definition AvailabilityCombinationsPerCell_r16__ext1O__F1 z :=
  (AvailabilityCombinationsPerCell_r16__ext1O__positionInDCI_AI_RBGroups_v1720 z, tt).
Definition AvailabilityCombinationsPerCell_r16__ext1O__F2 (y : seq_type AvailabilityCombinationsPerCell_r16__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__AvailabilityCombinationsPerCell_r16__ext1O__Type i0
  end.
Lemma AvailabilityCombinationsPerCell_r16__ext1O__F1F2_cond (z : AvailabilityCombinationsPerCell_r16__ext1O__Type)
  : AvailabilityCombinationsPerCell_r16__ext1O__cond z ->
  (seq_cond AvailabilityCombinationsPerCell_r16__ext1O__list (AvailabilityCombinationsPerCell_r16__ext1O__F1 z)).
intro H. unfold AvailabilityCombinationsPerCell_r16__ext1O__cond in H. simpl. auto. Qed.
Lemma AvailabilityCombinationsPerCell_r16__ext1O__F1F2_cond2 (z : AvailabilityCombinationsPerCell_r16__ext1O__Type)
 : AvailabilityCombinationsPerCell_r16__ext1O__F2 (AvailabilityCombinationsPerCell_r16__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AvailabilityCombinationsPerCell_r16__ext1O__F2F1_cond (y : seq_type AvailabilityCombinationsPerCell_r16__ext1O__list)
  : seq_cond AvailabilityCombinationsPerCell_r16__ext1O__list y ->
 (AvailabilityCombinationsPerCell_r16__ext1O__cond (AvailabilityCombinationsPerCell_r16__ext1O__F2 y)) /\  AvailabilityCombinationsPerCell_r16__ext1O__F1 (AvailabilityCombinationsPerCell_r16__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AvailabilityCombinationsPerCell_r16__ext1O__cond. simpl in *. auto.
 - simpl. unfold AvailabilityCombinationsPerCell_r16__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AvailabilityCombinationsPerCell_r16__ext1O__Format : T_Format AvailabilityCombinationsPerCell_r16__ext1O__Type AvailabilityCombinationsPerCell_r16__ext1O__cond :=
        proj2_format  AvailabilityCombinationsPerCell_r16__ext1O__cond AvailabilityCombinationsPerCell_r16__ext1O__list__Format
    AvailabilityCombinationsPerCell_r16__ext1O__F1 AvailabilityCombinationsPerCell_r16__ext1O__F2 AvailabilityCombinationsPerCell_r16__ext1O__F1F2_cond  AvailabilityCombinationsPerCell_r16__ext1O__F1F2_cond2 AvailabilityCombinationsPerCell_r16__ext1O__F2F1_cond.
Opaque AvailabilityCombinationsPerCell_r16__ext1O__cond AvailabilityCombinationsPerCell_r16__ext1O__Format.

Definition AvailabilityCombinationsPerCell_r16__ext1__check_all_none (b : AvailabilityCombinationsPerCell_r16__ext1O__Type) : bool :=
match b with 
  | make__AvailabilityCombinationsPerCell_r16__ext1O__Type None  => false 
  | _ => true 
 end.
Definition AvailabilityCombinationsPerCell_r16__ext1__Format : T_Format AvailabilityCombinationsPerCell_r16__ext1__Type AvailabilityCombinationsPerCell_r16__ext1__cond :=
  restrict_add_format AvailabilityCombinationsPerCell_r16__ext1__check_all_none AvailabilityCombinationsPerCell_r16__ext1O__Format.

Opaque AvailabilityCombinationsPerCell_r16__ext1__cond AvailabilityCombinationsPerCell_r16__ext1__Format.


Definition AvailabilityCombinationsPerCell_r16__root_Format_Type := Eval cbn in seq_format_prod AvailabilityCombinationsPerCell_r16__root_list.
Definition AvailabilityCombinationsPerCell_r16__root_Format_list : AvailabilityCombinationsPerCell_r16__root_Format_Type :=
  (AvailabilityCombinationsPerCellIndex_r16__Format, (CellIdentity__Format, (AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16__Format, (AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16__Format, unit_format)))).

Definition AvailabilityCombinationsPerCell_r16__ext_Format_Type := Eval cbn in get_formats AvailabilityCombinationsPerCell_r16__ext_list.
Definition AvailabilityCombinationsPerCell_r16__ext_Format_list : AvailabilityCombinationsPerCell_r16__ext_Format_Type :=
  (AvailabilityCombinationsPerCell_r16__ext0__Format, (AvailabilityCombinationsPerCell_r16__ext1__Format, unit__Format)).

Definition AvailabilityCombinationsPerCell_r16__list_type : Set := (seq_type AvailabilityCombinationsPerCell_r16__root_list) * (seq_ext_type AvailabilityCombinationsPerCell_r16__ext_list).
Definition AvailabilityCombinationsPerCell_r16__list_cond (z : AvailabilityCombinationsPerCell_r16__list_type) : Prop :=
        (seq_cond AvailabilityCombinationsPerCell_r16__root_list (fst z)) /\ (seq_ext_cond AvailabilityCombinationsPerCell_r16__ext_list (snd z)).
Definition AvailabilityCombinationsPerCell_r16__list_format : T_Format AvailabilityCombinationsPerCell_r16__list_type AvailabilityCombinationsPerCell_r16__list_cond :=
 (* Eval compute in *) seq_ext_format AvailabilityCombinationsPerCell_r16__root_list AvailabilityCombinationsPerCell_r16__root_Format_list AvailabilityCombinationsPerCell_r16__ext_list AvailabilityCombinationsPerCell_r16__ext_Format_list.

Opaque AvailabilityCombinationsPerCell_r16__list_format.
Definition AvailabilityCombinationsPerCell_r16__F1 (z : AvailabilityCombinationsPerCell_r16__Type) : AvailabilityCombinationsPerCell_r16__list_type :=
  (((AvailabilityCombinationsPerCell_r16__availabilityCombinationsPerCellIndex_r16 z, (AvailabilityCombinationsPerCell_r16__iab_DU_CellIdentity_r16 z, (AvailabilityCombinationsPerCell_r16__positionInDCI_AI_r16 z, (AvailabilityCombinationsPerCell_r16__availabilityCombinations_r16 z, tt))))), (
(AvailabilityCombinationsPerCell_r16__ext0 z, (AvailabilityCombinationsPerCell_r16__ext1 z, tt)))).
Definition AvailabilityCombinationsPerCell_r16__F2 (y : AvailabilityCombinationsPerCell_r16__list_type) : AvailabilityCombinationsPerCell_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__AvailabilityCombinationsPerCell_r16__Type j0 j1 j2 j3 i0 i1
  end.
Definition AvailabilityCombinationsPerCell_r16__helper1 : (forall a : AvailabilityCombinationsPerCell_r16__Type, AvailabilityCombinationsPerCell_r16__cond a -> AvailabilityCombinationsPerCell_r16__list_cond (AvailabilityCombinationsPerCell_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition AvailabilityCombinationsPerCell_r16__helper2 : (forall a : AvailabilityCombinationsPerCell_r16__Type, AvailabilityCombinationsPerCell_r16__F2 (AvailabilityCombinationsPerCell_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition AvailabilityCombinationsPerCell_r16__helper3 : (forall b : AvailabilityCombinationsPerCell_r16__list_type, AvailabilityCombinationsPerCell_r16__list_cond b -> AvailabilityCombinationsPerCell_r16__cond (AvailabilityCombinationsPerCell_r16__F2 b) /\ AvailabilityCombinationsPerCell_r16__F1 (AvailabilityCombinationsPerCell_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold AvailabilityCombinationsPerCell_r16__cond, AvailabilityCombinationsPerCell_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition AvailabilityCombinationsPerCell_r16__Format : T_Format AvailabilityCombinationsPerCell_r16__Type AvailabilityCombinationsPerCell_r16__cond :=
 proj2_format AvailabilityCombinationsPerCell_r16__cond AvailabilityCombinationsPerCell_r16__list_format  AvailabilityCombinationsPerCell_r16__F1 AvailabilityCombinationsPerCell_r16__F2 AvailabilityCombinationsPerCell_r16__helper1 AvailabilityCombinationsPerCell_r16__helper2 AvailabilityCombinationsPerCell_r16__helper3.

Opaque AvailabilityCombinationsPerCell_r16__cond AvailabilityCombinationsPerCell_r16__Format.

