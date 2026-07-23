Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__Type := Z.
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__cond := (fun z => (1 <= z <= 4)%Z).
Lemma FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__Type := Z.
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__cond := (fun z => (1 <= z <= 4)%Z).
Record FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Type : Set :=
  make__FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Type {
    FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet : Z ;
    FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx : Z ;
}.
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list := (
 Nor Z FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__cond ::
 Nor Z FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__cond ::
 nil).
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond z := 
  FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__cond (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet z) /\
  FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__cond (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx z) /\
  True.

Record FeatureSetUplinkPerCC_v1540__Type : Set :=
  make__FeatureSetUplinkPerCC_v1540__Type {
    FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH : option FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Type ;
}.
Definition FeatureSetUplinkPerCC_v1540__list := (
 Opt FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Type FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond ::
 nil).
Definition FeatureSetUplinkPerCC_v1540__cond z := 
  opt_cond FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH z) /\
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
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__Format : T_Format Z FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__cond :=
 ranged_int_format (1) (4) FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__helper1 FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__helper2.

Opaque FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__cond FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__Format.

Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__Format : T_Format Z FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__cond :=
 ranged_int_format (1) (4) FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__helper1 FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__helper2.

Opaque FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__cond FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__Format.


Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Format_Type := Eval cbn in seq_format_prod FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list.
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Format_list : FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Format_Type :=
  (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet__Format, (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx__Format, unit_format)).
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list__Format := (*Eval compute in *) seq_format FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Format_list.
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1 z :=
  (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSRS_ResourcePerSet z, (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__maxNumberSimultaneousSRS_ResourceTx z, tt)).
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F2 (y : seq_type FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Type i0 i1
  end.
Lemma FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1F2_cond (z : FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Type)
  : FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond z ->
  (seq_cond FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1 z)).
intro H. unfold FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1F2_cond2 (z : FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Type)
 : FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F2 (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F2F1_cond (y : seq_type FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list)
  : seq_cond FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list y ->
 (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F2 y)) /\  FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1 (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Format : T_Format FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Type FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond :=
        proj2_format  FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__list__Format
    FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1 FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F2 FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1F2_cond  FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F1F2_cond2 FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__F2F1_cond.
Opaque FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__cond FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Format.


Definition FeatureSetUplinkPerCC_v1540__Format_Type := Eval cbn in seq_format_prod FeatureSetUplinkPerCC_v1540__list.
Definition FeatureSetUplinkPerCC_v1540__Format_list : FeatureSetUplinkPerCC_v1540__Format_Type :=
  (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH__Format, unit_format).
Definition FeatureSetUplinkPerCC_v1540__list__Format := (*Eval compute in *) seq_format FeatureSetUplinkPerCC_v1540__list FeatureSetUplinkPerCC_v1540__Format_list.
Definition FeatureSetUplinkPerCC_v1540__F1 z :=
  (FeatureSetUplinkPerCC_v1540__mimo_NonCB_PUSCH z, tt).
Definition FeatureSetUplinkPerCC_v1540__F2 (y : seq_type FeatureSetUplinkPerCC_v1540__list) :=
  match y with
  | (i0, _)=>
    make__FeatureSetUplinkPerCC_v1540__Type i0
  end.
Lemma FeatureSetUplinkPerCC_v1540__F1F2_cond (z : FeatureSetUplinkPerCC_v1540__Type)
  : FeatureSetUplinkPerCC_v1540__cond z ->
  (seq_cond FeatureSetUplinkPerCC_v1540__list (FeatureSetUplinkPerCC_v1540__F1 z)).
intro H. unfold FeatureSetUplinkPerCC_v1540__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC_v1540__F1F2_cond2 (z : FeatureSetUplinkPerCC_v1540__Type)
 : FeatureSetUplinkPerCC_v1540__F2 (FeatureSetUplinkPerCC_v1540__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC_v1540__F2F1_cond (y : seq_type FeatureSetUplinkPerCC_v1540__list)
  : seq_cond FeatureSetUplinkPerCC_v1540__list y ->
 (FeatureSetUplinkPerCC_v1540__cond (FeatureSetUplinkPerCC_v1540__F2 y)) /\  FeatureSetUplinkPerCC_v1540__F1 (FeatureSetUplinkPerCC_v1540__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplinkPerCC_v1540__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplinkPerCC_v1540__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplinkPerCC_v1540__Format : T_Format FeatureSetUplinkPerCC_v1540__Type FeatureSetUplinkPerCC_v1540__cond :=
        proj2_format  FeatureSetUplinkPerCC_v1540__cond FeatureSetUplinkPerCC_v1540__list__Format
    FeatureSetUplinkPerCC_v1540__F1 FeatureSetUplinkPerCC_v1540__F2 FeatureSetUplinkPerCC_v1540__F1F2_cond  FeatureSetUplinkPerCC_v1540__F1F2_cond2 FeatureSetUplinkPerCC_v1540__F2F1_cond.
Opaque FeatureSetUplinkPerCC_v1540__cond FeatureSetUplinkPerCC_v1540__Format.

