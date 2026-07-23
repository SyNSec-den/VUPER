Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Lemma INT_ConfigurationPerServingCell__positionInDCI__helper1 : (0 <= maxINT_DCI_PayloadSize_1)%Z. unfold maxINT_DCI_PayloadSize_1.
 lia. Qed.
Lemma INT_ConfigurationPerServingCell__positionInDCI__helper2 : to_bit_sz (Z.to_nat (maxINT_DCI_PayloadSize_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxINT_DCI_PayloadSize_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply INT_ConfigurationPerServingCell__positionInDCI__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition INT_ConfigurationPerServingCell__positionInDCI__Type := Z.
Definition INT_ConfigurationPerServingCell__positionInDCI__cond := (fun z => (0 <= z <= maxINT_DCI_PayloadSize_1)%Z).
Record INT_ConfigurationPerServingCell__Type : Set :=
  make__INT_ConfigurationPerServingCell__Type {
    INT_ConfigurationPerServingCell__servingCellId : ServCellIndex__Type ;
    INT_ConfigurationPerServingCell__positionInDCI : Z ;
}.
Definition INT_ConfigurationPerServingCell__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor Z INT_ConfigurationPerServingCell__positionInDCI__cond ::
 nil).
Definition INT_ConfigurationPerServingCell__cond z := 
  ServCellIndex__cond (INT_ConfigurationPerServingCell__servingCellId z) /\
  INT_ConfigurationPerServingCell__positionInDCI__cond (INT_ConfigurationPerServingCell__positionInDCI z) /\
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
Definition INT_ConfigurationPerServingCell__positionInDCI__Format : T_Format Z INT_ConfigurationPerServingCell__positionInDCI__cond :=
 ranged_int_format (0) (maxINT_DCI_PayloadSize_1) INT_ConfigurationPerServingCell__positionInDCI__helper1 INT_ConfigurationPerServingCell__positionInDCI__helper2.

Opaque INT_ConfigurationPerServingCell__positionInDCI__cond INT_ConfigurationPerServingCell__positionInDCI__Format.


Definition INT_ConfigurationPerServingCell__Format_Type := Eval cbn in seq_format_prod INT_ConfigurationPerServingCell__list.
Definition INT_ConfigurationPerServingCell__Format_list : INT_ConfigurationPerServingCell__Format_Type :=
  (ServCellIndex__Format, (INT_ConfigurationPerServingCell__positionInDCI__Format, unit_format)).
Definition INT_ConfigurationPerServingCell__list__Format := (*Eval compute in *) seq_format INT_ConfigurationPerServingCell__list INT_ConfigurationPerServingCell__Format_list.
Definition INT_ConfigurationPerServingCell__F1 z :=
  (INT_ConfigurationPerServingCell__servingCellId z, (INT_ConfigurationPerServingCell__positionInDCI z, tt)).
Definition INT_ConfigurationPerServingCell__F2 (y : seq_type INT_ConfigurationPerServingCell__list) :=
  match y with
  | (i0, (i1, _))=>
    make__INT_ConfigurationPerServingCell__Type i0 i1
  end.
Lemma INT_ConfigurationPerServingCell__F1F2_cond (z : INT_ConfigurationPerServingCell__Type)
  : INT_ConfigurationPerServingCell__cond z ->
  (seq_cond INT_ConfigurationPerServingCell__list (INT_ConfigurationPerServingCell__F1 z)).
intro H. unfold INT_ConfigurationPerServingCell__cond in H. simpl. auto. Qed.
Lemma INT_ConfigurationPerServingCell__F1F2_cond2 (z : INT_ConfigurationPerServingCell__Type)
 : INT_ConfigurationPerServingCell__F2 (INT_ConfigurationPerServingCell__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma INT_ConfigurationPerServingCell__F2F1_cond (y : seq_type INT_ConfigurationPerServingCell__list)
  : seq_cond INT_ConfigurationPerServingCell__list y ->
 (INT_ConfigurationPerServingCell__cond (INT_ConfigurationPerServingCell__F2 y)) /\  INT_ConfigurationPerServingCell__F1 (INT_ConfigurationPerServingCell__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold INT_ConfigurationPerServingCell__cond. simpl in *. auto.
 - simpl. unfold INT_ConfigurationPerServingCell__F1. simpl. destruct_all_unit. auto.   Qed.
Definition INT_ConfigurationPerServingCell__Format : T_Format INT_ConfigurationPerServingCell__Type INT_ConfigurationPerServingCell__cond :=
        proj2_format  INT_ConfigurationPerServingCell__cond INT_ConfigurationPerServingCell__list__Format
    INT_ConfigurationPerServingCell__F1 INT_ConfigurationPerServingCell__F2 INT_ConfigurationPerServingCell__F1F2_cond  INT_ConfigurationPerServingCell__F1F2_cond2 INT_ConfigurationPerServingCell__F2F1_cond.
Opaque INT_ConfigurationPerServingCell__cond INT_ConfigurationPerServingCell__Format.

