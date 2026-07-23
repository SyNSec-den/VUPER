Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma TA_Info_r17__ta_Common_r17__helper1 : (0 <= 66485757)%Z.  lia. Qed.
Lemma TA_Info_r17__ta_Common_r17__helper2 : to_bit_sz (Z.to_nat (66485757 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (66485757 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TA_Info_r17__ta_Common_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TA_Info_r17__ta_Common_r17__Type := Z.
Definition TA_Info_r17__ta_Common_r17__cond := (fun z => (0 <= z <= 66485757)%Z).
Lemma TA_Info_r17__ta_CommonDrift_r17__helper1 : (-257303 <= 257303)%Z.  lia. Qed.
Lemma TA_Info_r17__ta_CommonDrift_r17__helper2 : to_bit_sz (Z.to_nat (257303 - -257303)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (257303 - -257303))%Z). { apply Zorder.Zle_minus_le_0. apply TA_Info_r17__ta_CommonDrift_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TA_Info_r17__ta_CommonDrift_r17__Type := Z.
Definition TA_Info_r17__ta_CommonDrift_r17__cond := (fun z => (-257303 <= z <= 257303)%Z).
Lemma TA_Info_r17__ta_CommonDriftVariant_r17__helper1 : (0 <= 28949)%Z.  lia. Qed.
Lemma TA_Info_r17__ta_CommonDriftVariant_r17__helper2 : to_bit_sz (Z.to_nat (28949 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (28949 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TA_Info_r17__ta_CommonDriftVariant_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TA_Info_r17__ta_CommonDriftVariant_r17__Type := Z.
Definition TA_Info_r17__ta_CommonDriftVariant_r17__cond := (fun z => (0 <= z <= 28949)%Z).
Record TA_Info_r17__Type : Set :=
  make__TA_Info_r17__Type {
    TA_Info_r17__ta_Common_r17 : Z ;
    TA_Info_r17__ta_CommonDrift_r17 : option Z ;
    TA_Info_r17__ta_CommonDriftVariant_r17 : option Z ;
}.
Definition TA_Info_r17__list := (
 Nor Z TA_Info_r17__ta_Common_r17__cond ::
 Opt Z TA_Info_r17__ta_CommonDrift_r17__cond ::
 Opt Z TA_Info_r17__ta_CommonDriftVariant_r17__cond ::
 nil).
Definition TA_Info_r17__cond z := 
  TA_Info_r17__ta_Common_r17__cond (TA_Info_r17__ta_Common_r17 z) /\
  opt_cond TA_Info_r17__ta_CommonDrift_r17__cond (TA_Info_r17__ta_CommonDrift_r17 z) /\
  opt_cond TA_Info_r17__ta_CommonDriftVariant_r17__cond (TA_Info_r17__ta_CommonDriftVariant_r17 z) /\
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
Definition TA_Info_r17__ta_Common_r17__Format : T_Format Z TA_Info_r17__ta_Common_r17__cond :=
 ranged_int_format (0) (66485757) TA_Info_r17__ta_Common_r17__helper1 TA_Info_r17__ta_Common_r17__helper2.

Opaque TA_Info_r17__ta_Common_r17__cond TA_Info_r17__ta_Common_r17__Format.

Definition TA_Info_r17__ta_CommonDrift_r17__Format : T_Format Z TA_Info_r17__ta_CommonDrift_r17__cond :=
 ranged_int_format (-257303) (257303) TA_Info_r17__ta_CommonDrift_r17__helper1 TA_Info_r17__ta_CommonDrift_r17__helper2.

Opaque TA_Info_r17__ta_CommonDrift_r17__cond TA_Info_r17__ta_CommonDrift_r17__Format.

Definition TA_Info_r17__ta_CommonDriftVariant_r17__Format : T_Format Z TA_Info_r17__ta_CommonDriftVariant_r17__cond :=
 ranged_int_format (0) (28949) TA_Info_r17__ta_CommonDriftVariant_r17__helper1 TA_Info_r17__ta_CommonDriftVariant_r17__helper2.

Opaque TA_Info_r17__ta_CommonDriftVariant_r17__cond TA_Info_r17__ta_CommonDriftVariant_r17__Format.


Definition TA_Info_r17__Format_Type := Eval cbn in seq_format_prod TA_Info_r17__list.
Definition TA_Info_r17__Format_list : TA_Info_r17__Format_Type :=
  (TA_Info_r17__ta_Common_r17__Format, (TA_Info_r17__ta_CommonDrift_r17__Format, (TA_Info_r17__ta_CommonDriftVariant_r17__Format, unit_format))).
Definition TA_Info_r17__list__Format := (*Eval compute in *) seq_format TA_Info_r17__list TA_Info_r17__Format_list.
Definition TA_Info_r17__F1 z :=
  (TA_Info_r17__ta_Common_r17 z, (TA_Info_r17__ta_CommonDrift_r17 z, (TA_Info_r17__ta_CommonDriftVariant_r17 z, tt))).
Definition TA_Info_r17__F2 (y : seq_type TA_Info_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__TA_Info_r17__Type i0 i1 i2
  end.
Lemma TA_Info_r17__F1F2_cond (z : TA_Info_r17__Type)
  : TA_Info_r17__cond z ->
  (seq_cond TA_Info_r17__list (TA_Info_r17__F1 z)).
intro H. unfold TA_Info_r17__cond in H. simpl. auto. Qed.
Lemma TA_Info_r17__F1F2_cond2 (z : TA_Info_r17__Type)
 : TA_Info_r17__F2 (TA_Info_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TA_Info_r17__F2F1_cond (y : seq_type TA_Info_r17__list)
  : seq_cond TA_Info_r17__list y ->
 (TA_Info_r17__cond (TA_Info_r17__F2 y)) /\  TA_Info_r17__F1 (TA_Info_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TA_Info_r17__cond. simpl in *. auto.
 - simpl. unfold TA_Info_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TA_Info_r17__Format : T_Format TA_Info_r17__Type TA_Info_r17__cond :=
        proj2_format  TA_Info_r17__cond TA_Info_r17__list__Format
    TA_Info_r17__F1 TA_Info_r17__F2 TA_Info_r17__F1F2_cond  TA_Info_r17__F1F2_cond2 TA_Info_r17__F2F1_cond.
Opaque TA_Info_r17__cond TA_Info_r17__Format.

