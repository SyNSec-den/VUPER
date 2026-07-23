Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.P0_PUCCH_Id.

Opaque P0_PUCCH_Id__cond P0_PUCCH_Id__Format.

Lemma P0_PUCCH__p0_PUCCH_Value__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma P0_PUCCH__p0_PUCCH_Value__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply P0_PUCCH__p0_PUCCH_Value__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition P0_PUCCH__p0_PUCCH_Value__Type := Z.
Definition P0_PUCCH__p0_PUCCH_Value__cond := (fun z => (-16 <= z <= 15)%Z).
Record P0_PUCCH__Type : Set :=
  make__P0_PUCCH__Type {
    P0_PUCCH__p0_PUCCH_Id : P0_PUCCH_Id__Type ;
    P0_PUCCH__p0_PUCCH_Value : Z ;
}.
Definition P0_PUCCH__list := (
 Nor P0_PUCCH_Id__Type P0_PUCCH_Id__cond ::
 Nor Z P0_PUCCH__p0_PUCCH_Value__cond ::
 nil).
Definition P0_PUCCH__cond z := 
  P0_PUCCH_Id__cond (P0_PUCCH__p0_PUCCH_Id z) /\
  P0_PUCCH__p0_PUCCH_Value__cond (P0_PUCCH__p0_PUCCH_Value z) /\
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
Definition P0_PUCCH__p0_PUCCH_Value__Format : T_Format Z P0_PUCCH__p0_PUCCH_Value__cond :=
 ranged_int_format (-16) (15) P0_PUCCH__p0_PUCCH_Value__helper1 P0_PUCCH__p0_PUCCH_Value__helper2.

Opaque P0_PUCCH__p0_PUCCH_Value__cond P0_PUCCH__p0_PUCCH_Value__Format.


Definition P0_PUCCH__Format_Type := Eval cbn in seq_format_prod P0_PUCCH__list.
Definition P0_PUCCH__Format_list : P0_PUCCH__Format_Type :=
  (P0_PUCCH_Id__Format, (P0_PUCCH__p0_PUCCH_Value__Format, unit_format)).
Definition P0_PUCCH__list__Format := (*Eval compute in *) seq_format P0_PUCCH__list P0_PUCCH__Format_list.
Definition P0_PUCCH__F1 z :=
  (P0_PUCCH__p0_PUCCH_Id z, (P0_PUCCH__p0_PUCCH_Value z, tt)).
Definition P0_PUCCH__F2 (y : seq_type P0_PUCCH__list) :=
  match y with
  | (i0, (i1, _))=>
    make__P0_PUCCH__Type i0 i1
  end.
Lemma P0_PUCCH__F1F2_cond (z : P0_PUCCH__Type)
  : P0_PUCCH__cond z ->
  (seq_cond P0_PUCCH__list (P0_PUCCH__F1 z)).
intro H. unfold P0_PUCCH__cond in H. simpl. auto. Qed.
Lemma P0_PUCCH__F1F2_cond2 (z : P0_PUCCH__Type)
 : P0_PUCCH__F2 (P0_PUCCH__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma P0_PUCCH__F2F1_cond (y : seq_type P0_PUCCH__list)
  : seq_cond P0_PUCCH__list y ->
 (P0_PUCCH__cond (P0_PUCCH__F2 y)) /\  P0_PUCCH__F1 (P0_PUCCH__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold P0_PUCCH__cond. simpl in *. auto.
 - simpl. unfold P0_PUCCH__F1. simpl. destruct_all_unit. auto.   Qed.
Definition P0_PUCCH__Format : T_Format P0_PUCCH__Type P0_PUCCH__cond :=
        proj2_format  P0_PUCCH__cond P0_PUCCH__list__Format
    P0_PUCCH__F1 P0_PUCCH__F2 P0_PUCCH__F1F2_cond  P0_PUCCH__F1F2_cond2 P0_PUCCH__F2F1_cond.
Opaque P0_PUCCH__cond P0_PUCCH__Format.

