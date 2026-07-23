Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma UAC_BarringPerCat__accessCategory__helper1 : (1 <= maxAccessCat_1)%Z. unfold maxAccessCat_1.
 lia. Qed.
Lemma UAC_BarringPerCat__accessCategory__helper2 : to_bit_sz (Z.to_nat (maxAccessCat_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxAccessCat_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UAC_BarringPerCat__accessCategory__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UAC_BarringPerCat__accessCategory__Type := Z.
Definition UAC_BarringPerCat__accessCategory__cond := (fun z => (1 <= z <= maxAccessCat_1)%Z).
Require Import NR.UAC_BarringInfoSetIndex.

Opaque UAC_BarringInfoSetIndex__cond UAC_BarringInfoSetIndex__Format.

Record UAC_BarringPerCat__Type : Set :=
  make__UAC_BarringPerCat__Type {
    UAC_BarringPerCat__accessCategory : Z ;
    UAC_BarringPerCat__uac_barringInfoSetIndex : UAC_BarringInfoSetIndex__Type ;
}.
Definition UAC_BarringPerCat__list := (
 Nor Z UAC_BarringPerCat__accessCategory__cond ::
 Nor UAC_BarringInfoSetIndex__Type UAC_BarringInfoSetIndex__cond ::
 nil).
Definition UAC_BarringPerCat__cond z := 
  UAC_BarringPerCat__accessCategory__cond (UAC_BarringPerCat__accessCategory z) /\
  UAC_BarringInfoSetIndex__cond (UAC_BarringPerCat__uac_barringInfoSetIndex z) /\
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
Definition UAC_BarringPerCat__accessCategory__Format : T_Format Z UAC_BarringPerCat__accessCategory__cond :=
 ranged_int_format (1) (maxAccessCat_1) UAC_BarringPerCat__accessCategory__helper1 UAC_BarringPerCat__accessCategory__helper2.

Opaque UAC_BarringPerCat__accessCategory__cond UAC_BarringPerCat__accessCategory__Format.


Definition UAC_BarringPerCat__Format_Type := Eval cbn in seq_format_prod UAC_BarringPerCat__list.
Definition UAC_BarringPerCat__Format_list : UAC_BarringPerCat__Format_Type :=
  (UAC_BarringPerCat__accessCategory__Format, (UAC_BarringInfoSetIndex__Format, unit_format)).
Definition UAC_BarringPerCat__list__Format := (*Eval compute in *) seq_format UAC_BarringPerCat__list UAC_BarringPerCat__Format_list.
Definition UAC_BarringPerCat__F1 z :=
  (UAC_BarringPerCat__accessCategory z, (UAC_BarringPerCat__uac_barringInfoSetIndex z, tt)).
Definition UAC_BarringPerCat__F2 (y : seq_type UAC_BarringPerCat__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UAC_BarringPerCat__Type i0 i1
  end.
Lemma UAC_BarringPerCat__F1F2_cond (z : UAC_BarringPerCat__Type)
  : UAC_BarringPerCat__cond z ->
  (seq_cond UAC_BarringPerCat__list (UAC_BarringPerCat__F1 z)).
intro H. unfold UAC_BarringPerCat__cond in H. simpl. auto. Qed.
Lemma UAC_BarringPerCat__F1F2_cond2 (z : UAC_BarringPerCat__Type)
 : UAC_BarringPerCat__F2 (UAC_BarringPerCat__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UAC_BarringPerCat__F2F1_cond (y : seq_type UAC_BarringPerCat__list)
  : seq_cond UAC_BarringPerCat__list y ->
 (UAC_BarringPerCat__cond (UAC_BarringPerCat__F2 y)) /\  UAC_BarringPerCat__F1 (UAC_BarringPerCat__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UAC_BarringPerCat__cond. simpl in *. auto.
 - simpl. unfold UAC_BarringPerCat__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UAC_BarringPerCat__Format : T_Format UAC_BarringPerCat__Type UAC_BarringPerCat__cond :=
        proj2_format  UAC_BarringPerCat__cond UAC_BarringPerCat__list__Format
    UAC_BarringPerCat__F1 UAC_BarringPerCat__F2 UAC_BarringPerCat__F1F2_cond  UAC_BarringPerCat__F1F2_cond2 UAC_BarringPerCat__F2F1_cond.
Opaque UAC_BarringPerCat__cond UAC_BarringPerCat__Format.

