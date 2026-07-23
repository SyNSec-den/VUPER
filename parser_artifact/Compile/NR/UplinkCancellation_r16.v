Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Lemma UplinkCancellation_r16__dci_PayloadSizeForCI_r16__helper1 : (0 <= maxCI_DCI_PayloadSize_r16)%Z. unfold maxCI_DCI_PayloadSize_r16.
 lia. Qed.
Lemma UplinkCancellation_r16__dci_PayloadSizeForCI_r16__helper2 : to_bit_sz (Z.to_nat (maxCI_DCI_PayloadSize_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCI_DCI_PayloadSize_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply UplinkCancellation_r16__dci_PayloadSizeForCI_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UplinkCancellation_r16__dci_PayloadSizeForCI_r16__Type := Z.
Definition UplinkCancellation_r16__dci_PayloadSizeForCI_r16__cond := (fun z => (0 <= z <= maxCI_DCI_PayloadSize_r16)%Z).
Require Import NR.CI_ConfigurationPerServingCell_r16.

Opaque CI_ConfigurationPerServingCell_r16__cond CI_ConfigurationPerServingCell_r16__Format.

Definition UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__Type := list CI_ConfigurationPerServingCell_r16__Type.

Lemma UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__cond (z : UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells)%Z /\ (list_and CI_ConfigurationPerServingCell_r16__cond z) .

Record UplinkCancellation_r16__Type : Set :=
  make__UplinkCancellation_r16__Type {
    UplinkCancellation_r16__ci_RNTI_r16 : RNTI_Value__Type ;
    UplinkCancellation_r16__dci_PayloadSizeForCI_r16 : Z ;
    UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16 : UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__Type ;
}.
Definition UplinkCancellation_r16__root_list : list seq_elem := (
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Nor Z UplinkCancellation_r16__dci_PayloadSizeForCI_r16__cond ::
 Nor UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__Type UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__cond ::
 nil).
Definition UplinkCancellation_r16__ext_list : list typ := (
  nil).
Definition UplinkCancellation_r16__cond (z : UplinkCancellation_r16__Type) := 
(  RNTI_Value__cond (UplinkCancellation_r16__ci_RNTI_r16 z) /\
  UplinkCancellation_r16__dci_PayloadSizeForCI_r16__cond (UplinkCancellation_r16__dci_PayloadSizeForCI_r16 z) /\
  UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__cond (UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16 z) /\
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
Definition UplinkCancellation_r16__dci_PayloadSizeForCI_r16__Format : T_Format Z UplinkCancellation_r16__dci_PayloadSizeForCI_r16__cond :=
 ranged_int_format (0) (maxCI_DCI_PayloadSize_r16) UplinkCancellation_r16__dci_PayloadSizeForCI_r16__helper1 UplinkCancellation_r16__dci_PayloadSizeForCI_r16__helper2.

Opaque UplinkCancellation_r16__dci_PayloadSizeForCI_r16__cond UplinkCancellation_r16__dci_PayloadSizeForCI_r16__Format.

Definition UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__Format : T_Format UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__Type UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__cond := seq_of_format CI_ConfigurationPerServingCell_r16__Format 1 maxNrofServingCells UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__helper1 UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__helper2.

Opaque UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__cond UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__Format.


Definition UplinkCancellation_r16__root_Format_Type := Eval cbn in seq_format_prod UplinkCancellation_r16__root_list.
Definition UplinkCancellation_r16__root_Format_list : UplinkCancellation_r16__root_Format_Type :=
  (RNTI_Value__Format, (UplinkCancellation_r16__dci_PayloadSizeForCI_r16__Format, (UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16__Format, unit_format))).

Definition UplinkCancellation_r16__ext_Format_Type := Eval cbn in get_formats UplinkCancellation_r16__ext_list.
Definition UplinkCancellation_r16__ext_Format_list : UplinkCancellation_r16__ext_Format_Type :=
  unit__Format.

Definition UplinkCancellation_r16__list_type : Set := (seq_type UplinkCancellation_r16__root_list) * (seq_ext_type UplinkCancellation_r16__ext_list).
Definition UplinkCancellation_r16__list_cond (z : UplinkCancellation_r16__list_type) : Prop :=
        (seq_cond UplinkCancellation_r16__root_list (fst z)) /\ (seq_ext_cond UplinkCancellation_r16__ext_list (snd z)).
Definition UplinkCancellation_r16__list_format : T_Format UplinkCancellation_r16__list_type UplinkCancellation_r16__list_cond :=
 (* Eval compute in *) seq_ext_format UplinkCancellation_r16__root_list UplinkCancellation_r16__root_Format_list UplinkCancellation_r16__ext_list UplinkCancellation_r16__ext_Format_list.

Opaque UplinkCancellation_r16__list_format.
Definition UplinkCancellation_r16__F1 (z : UplinkCancellation_r16__Type) : UplinkCancellation_r16__list_type :=
  (((UplinkCancellation_r16__ci_RNTI_r16 z, (UplinkCancellation_r16__dci_PayloadSizeForCI_r16 z, (UplinkCancellation_r16__ci_ConfigurationPerServingCell_r16 z, tt)))), (
tt)).
Definition UplinkCancellation_r16__F2 (y : UplinkCancellation_r16__list_type) : UplinkCancellation_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__UplinkCancellation_r16__Type j0 j1 j2
  end.
Definition UplinkCancellation_r16__helper1 : (forall a : UplinkCancellation_r16__Type, UplinkCancellation_r16__cond a -> UplinkCancellation_r16__list_cond (UplinkCancellation_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition UplinkCancellation_r16__helper2 : (forall a : UplinkCancellation_r16__Type, UplinkCancellation_r16__F2 (UplinkCancellation_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition UplinkCancellation_r16__helper3 : (forall b : UplinkCancellation_r16__list_type, UplinkCancellation_r16__list_cond b -> UplinkCancellation_r16__cond (UplinkCancellation_r16__F2 b) /\ UplinkCancellation_r16__F1 (UplinkCancellation_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold UplinkCancellation_r16__cond, UplinkCancellation_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition UplinkCancellation_r16__Format : T_Format UplinkCancellation_r16__Type UplinkCancellation_r16__cond :=
 proj2_format UplinkCancellation_r16__cond UplinkCancellation_r16__list_format  UplinkCancellation_r16__F1 UplinkCancellation_r16__F2 UplinkCancellation_r16__helper1 UplinkCancellation_r16__helper2 UplinkCancellation_r16__helper3.

Opaque UplinkCancellation_r16__cond UplinkCancellation_r16__Format.

