Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SRS_CC_SetIndex__cc_SetIndex__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SRS_CC_SetIndex__cc_SetIndex__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_CC_SetIndex__cc_SetIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_CC_SetIndex__cc_SetIndex__Type := Z.
Definition SRS_CC_SetIndex__cc_SetIndex__cond := (fun z => (0 <= z <= 3)%Z).
Lemma SRS_CC_SetIndex__cc_IndexInOneCC_Set__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma SRS_CC_SetIndex__cc_IndexInOneCC_Set__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_CC_SetIndex__cc_IndexInOneCC_Set__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_CC_SetIndex__cc_IndexInOneCC_Set__Type := Z.
Definition SRS_CC_SetIndex__cc_IndexInOneCC_Set__cond := (fun z => (0 <= z <= 7)%Z).
Record SRS_CC_SetIndex__Type : Set :=
  make__SRS_CC_SetIndex__Type {
    SRS_CC_SetIndex__cc_SetIndex : option Z ;
    SRS_CC_SetIndex__cc_IndexInOneCC_Set : option Z ;
}.
Definition SRS_CC_SetIndex__list := (
 Opt Z SRS_CC_SetIndex__cc_SetIndex__cond ::
 Opt Z SRS_CC_SetIndex__cc_IndexInOneCC_Set__cond ::
 nil).
Definition SRS_CC_SetIndex__cond z := 
  opt_cond SRS_CC_SetIndex__cc_SetIndex__cond (SRS_CC_SetIndex__cc_SetIndex z) /\
  opt_cond SRS_CC_SetIndex__cc_IndexInOneCC_Set__cond (SRS_CC_SetIndex__cc_IndexInOneCC_Set z) /\
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
Definition SRS_CC_SetIndex__cc_SetIndex__Format : T_Format Z SRS_CC_SetIndex__cc_SetIndex__cond :=
 ranged_int_format (0) (3) SRS_CC_SetIndex__cc_SetIndex__helper1 SRS_CC_SetIndex__cc_SetIndex__helper2.

Opaque SRS_CC_SetIndex__cc_SetIndex__cond SRS_CC_SetIndex__cc_SetIndex__Format.

Definition SRS_CC_SetIndex__cc_IndexInOneCC_Set__Format : T_Format Z SRS_CC_SetIndex__cc_IndexInOneCC_Set__cond :=
 ranged_int_format (0) (7) SRS_CC_SetIndex__cc_IndexInOneCC_Set__helper1 SRS_CC_SetIndex__cc_IndexInOneCC_Set__helper2.

Opaque SRS_CC_SetIndex__cc_IndexInOneCC_Set__cond SRS_CC_SetIndex__cc_IndexInOneCC_Set__Format.


Definition SRS_CC_SetIndex__Format_Type := Eval cbn in seq_format_prod SRS_CC_SetIndex__list.
Definition SRS_CC_SetIndex__Format_list : SRS_CC_SetIndex__Format_Type :=
  (SRS_CC_SetIndex__cc_SetIndex__Format, (SRS_CC_SetIndex__cc_IndexInOneCC_Set__Format, unit_format)).
Definition SRS_CC_SetIndex__list__Format := (*Eval compute in *) seq_format SRS_CC_SetIndex__list SRS_CC_SetIndex__Format_list.
Definition SRS_CC_SetIndex__F1 z :=
  (SRS_CC_SetIndex__cc_SetIndex z, (SRS_CC_SetIndex__cc_IndexInOneCC_Set z, tt)).
Definition SRS_CC_SetIndex__F2 (y : seq_type SRS_CC_SetIndex__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_CC_SetIndex__Type i0 i1
  end.
Lemma SRS_CC_SetIndex__F1F2_cond (z : SRS_CC_SetIndex__Type)
  : SRS_CC_SetIndex__cond z ->
  (seq_cond SRS_CC_SetIndex__list (SRS_CC_SetIndex__F1 z)).
intro H. unfold SRS_CC_SetIndex__cond in H. simpl. auto. Qed.
Lemma SRS_CC_SetIndex__F1F2_cond2 (z : SRS_CC_SetIndex__Type)
 : SRS_CC_SetIndex__F2 (SRS_CC_SetIndex__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_CC_SetIndex__F2F1_cond (y : seq_type SRS_CC_SetIndex__list)
  : seq_cond SRS_CC_SetIndex__list y ->
 (SRS_CC_SetIndex__cond (SRS_CC_SetIndex__F2 y)) /\  SRS_CC_SetIndex__F1 (SRS_CC_SetIndex__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_CC_SetIndex__cond. simpl in *. auto.
 - simpl. unfold SRS_CC_SetIndex__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_CC_SetIndex__Format : T_Format SRS_CC_SetIndex__Type SRS_CC_SetIndex__cond :=
        proj2_format  SRS_CC_SetIndex__cond SRS_CC_SetIndex__list__Format
    SRS_CC_SetIndex__F1 SRS_CC_SetIndex__F2 SRS_CC_SetIndex__F1F2_cond  SRS_CC_SetIndex__F1F2_cond2 SRS_CC_SetIndex__F2F1_cond.
Opaque SRS_CC_SetIndex__cond SRS_CC_SetIndex__Format.

