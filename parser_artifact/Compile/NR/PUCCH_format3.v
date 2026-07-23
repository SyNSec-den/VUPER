Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUCCH_format3__nrofPRBs__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma PUCCH_format3__nrofPRBs__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_format3__nrofPRBs__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_format3__nrofPRBs__Type := Z.
Definition PUCCH_format3__nrofPRBs__cond := (fun z => (1 <= z <= 16)%Z).
Lemma PUCCH_format3__nrofSymbols__helper1 : (4 <= 14)%Z.  lia. Qed.
Lemma PUCCH_format3__nrofSymbols__helper2 : to_bit_sz (Z.to_nat (14 - 4)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (14 - 4))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_format3__nrofSymbols__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_format3__nrofSymbols__Type := Z.
Definition PUCCH_format3__nrofSymbols__cond := (fun z => (4 <= z <= 14)%Z).
Lemma PUCCH_format3__startingSymbolIndex__helper1 : (0 <= 10)%Z.  lia. Qed.
Lemma PUCCH_format3__startingSymbolIndex__helper2 : to_bit_sz (Z.to_nat (10 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_format3__startingSymbolIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_format3__startingSymbolIndex__Type := Z.
Definition PUCCH_format3__startingSymbolIndex__cond := (fun z => (0 <= z <= 10)%Z).
Record PUCCH_format3__Type : Set :=
  make__PUCCH_format3__Type {
    PUCCH_format3__nrofPRBs : Z ;
    PUCCH_format3__nrofSymbols : Z ;
    PUCCH_format3__startingSymbolIndex : Z ;
}.
Definition PUCCH_format3__list := (
 Nor Z PUCCH_format3__nrofPRBs__cond ::
 Nor Z PUCCH_format3__nrofSymbols__cond ::
 Nor Z PUCCH_format3__startingSymbolIndex__cond ::
 nil).
Definition PUCCH_format3__cond z := 
  PUCCH_format3__nrofPRBs__cond (PUCCH_format3__nrofPRBs z) /\
  PUCCH_format3__nrofSymbols__cond (PUCCH_format3__nrofSymbols z) /\
  PUCCH_format3__startingSymbolIndex__cond (PUCCH_format3__startingSymbolIndex z) /\
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
Definition PUCCH_format3__nrofPRBs__Format : T_Format Z PUCCH_format3__nrofPRBs__cond :=
 ranged_int_format (1) (16) PUCCH_format3__nrofPRBs__helper1 PUCCH_format3__nrofPRBs__helper2.

Opaque PUCCH_format3__nrofPRBs__cond PUCCH_format3__nrofPRBs__Format.

Definition PUCCH_format3__nrofSymbols__Format : T_Format Z PUCCH_format3__nrofSymbols__cond :=
 ranged_int_format (4) (14) PUCCH_format3__nrofSymbols__helper1 PUCCH_format3__nrofSymbols__helper2.

Opaque PUCCH_format3__nrofSymbols__cond PUCCH_format3__nrofSymbols__Format.

Definition PUCCH_format3__startingSymbolIndex__Format : T_Format Z PUCCH_format3__startingSymbolIndex__cond :=
 ranged_int_format (0) (10) PUCCH_format3__startingSymbolIndex__helper1 PUCCH_format3__startingSymbolIndex__helper2.

Opaque PUCCH_format3__startingSymbolIndex__cond PUCCH_format3__startingSymbolIndex__Format.


Definition PUCCH_format3__Format_Type := Eval cbn in seq_format_prod PUCCH_format3__list.
Definition PUCCH_format3__Format_list : PUCCH_format3__Format_Type :=
  (PUCCH_format3__nrofPRBs__Format, (PUCCH_format3__nrofSymbols__Format, (PUCCH_format3__startingSymbolIndex__Format, unit_format))).
Definition PUCCH_format3__list__Format := (*Eval compute in *) seq_format PUCCH_format3__list PUCCH_format3__Format_list.
Definition PUCCH_format3__F1 z :=
  (PUCCH_format3__nrofPRBs z, (PUCCH_format3__nrofSymbols z, (PUCCH_format3__startingSymbolIndex z, tt))).
Definition PUCCH_format3__F2 (y : seq_type PUCCH_format3__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PUCCH_format3__Type i0 i1 i2
  end.
Lemma PUCCH_format3__F1F2_cond (z : PUCCH_format3__Type)
  : PUCCH_format3__cond z ->
  (seq_cond PUCCH_format3__list (PUCCH_format3__F1 z)).
intro H. unfold PUCCH_format3__cond in H. simpl. auto. Qed.
Lemma PUCCH_format3__F1F2_cond2 (z : PUCCH_format3__Type)
 : PUCCH_format3__F2 (PUCCH_format3__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_format3__F2F1_cond (y : seq_type PUCCH_format3__list)
  : seq_cond PUCCH_format3__list y ->
 (PUCCH_format3__cond (PUCCH_format3__F2 y)) /\  PUCCH_format3__F1 (PUCCH_format3__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_format3__cond. simpl in *. auto.
 - simpl. unfold PUCCH_format3__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_format3__Format : T_Format PUCCH_format3__Type PUCCH_format3__cond :=
        proj2_format  PUCCH_format3__cond PUCCH_format3__list__Format
    PUCCH_format3__F1 PUCCH_format3__F2 PUCCH_format3__F1F2_cond  PUCCH_format3__F1F2_cond2 PUCCH_format3__F2F1_cond.
Opaque PUCCH_format3__cond PUCCH_format3__Format.

