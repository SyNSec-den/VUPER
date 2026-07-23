Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.P0_PUSCH_AlphaSetId.

Opaque P0_PUSCH_AlphaSetId__cond P0_PUSCH_AlphaSetId__Format.

Lemma P0_PUSCH_AlphaSet__p0__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma P0_PUSCH_AlphaSet__p0__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply P0_PUSCH_AlphaSet__p0__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition P0_PUSCH_AlphaSet__p0__Type := Z.
Definition P0_PUSCH_AlphaSet__p0__cond := (fun z => (-16 <= z <= 15)%Z).
Require Import NR.Alpha.

Opaque Alpha__cond Alpha__Format.

Record P0_PUSCH_AlphaSet__Type : Set :=
  make__P0_PUSCH_AlphaSet__Type {
    P0_PUSCH_AlphaSet__p0_PUSCH_AlphaSetId : P0_PUSCH_AlphaSetId__Type ;
    P0_PUSCH_AlphaSet__p0 : option Z ;
    P0_PUSCH_AlphaSet__alpha : option Alpha__Type ;
}.
Definition P0_PUSCH_AlphaSet__list := (
 Nor P0_PUSCH_AlphaSetId__Type P0_PUSCH_AlphaSetId__cond ::
 Opt Z P0_PUSCH_AlphaSet__p0__cond ::
 Opt Alpha__Type Alpha__cond ::
 nil).
Definition P0_PUSCH_AlphaSet__cond z := 
  P0_PUSCH_AlphaSetId__cond (P0_PUSCH_AlphaSet__p0_PUSCH_AlphaSetId z) /\
  opt_cond P0_PUSCH_AlphaSet__p0__cond (P0_PUSCH_AlphaSet__p0 z) /\
  opt_cond Alpha__cond (P0_PUSCH_AlphaSet__alpha z) /\
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
Definition P0_PUSCH_AlphaSet__p0__Format : T_Format Z P0_PUSCH_AlphaSet__p0__cond :=
 ranged_int_format (-16) (15) P0_PUSCH_AlphaSet__p0__helper1 P0_PUSCH_AlphaSet__p0__helper2.

Opaque P0_PUSCH_AlphaSet__p0__cond P0_PUSCH_AlphaSet__p0__Format.


Definition P0_PUSCH_AlphaSet__Format_Type := Eval cbn in seq_format_prod P0_PUSCH_AlphaSet__list.
Definition P0_PUSCH_AlphaSet__Format_list : P0_PUSCH_AlphaSet__Format_Type :=
  (P0_PUSCH_AlphaSetId__Format, (P0_PUSCH_AlphaSet__p0__Format, (Alpha__Format, unit_format))).
Definition P0_PUSCH_AlphaSet__list__Format := (*Eval compute in *) seq_format P0_PUSCH_AlphaSet__list P0_PUSCH_AlphaSet__Format_list.
Definition P0_PUSCH_AlphaSet__F1 z :=
  (P0_PUSCH_AlphaSet__p0_PUSCH_AlphaSetId z, (P0_PUSCH_AlphaSet__p0 z, (P0_PUSCH_AlphaSet__alpha z, tt))).
Definition P0_PUSCH_AlphaSet__F2 (y : seq_type P0_PUSCH_AlphaSet__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__P0_PUSCH_AlphaSet__Type i0 i1 i2
  end.
Lemma P0_PUSCH_AlphaSet__F1F2_cond (z : P0_PUSCH_AlphaSet__Type)
  : P0_PUSCH_AlphaSet__cond z ->
  (seq_cond P0_PUSCH_AlphaSet__list (P0_PUSCH_AlphaSet__F1 z)).
intro H. unfold P0_PUSCH_AlphaSet__cond in H. simpl. auto. Qed.
Lemma P0_PUSCH_AlphaSet__F1F2_cond2 (z : P0_PUSCH_AlphaSet__Type)
 : P0_PUSCH_AlphaSet__F2 (P0_PUSCH_AlphaSet__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma P0_PUSCH_AlphaSet__F2F1_cond (y : seq_type P0_PUSCH_AlphaSet__list)
  : seq_cond P0_PUSCH_AlphaSet__list y ->
 (P0_PUSCH_AlphaSet__cond (P0_PUSCH_AlphaSet__F2 y)) /\  P0_PUSCH_AlphaSet__F1 (P0_PUSCH_AlphaSet__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold P0_PUSCH_AlphaSet__cond. simpl in *. auto.
 - simpl. unfold P0_PUSCH_AlphaSet__F1. simpl. destruct_all_unit. auto.   Qed.
Definition P0_PUSCH_AlphaSet__Format : T_Format P0_PUSCH_AlphaSet__Type P0_PUSCH_AlphaSet__cond :=
        proj2_format  P0_PUSCH_AlphaSet__cond P0_PUSCH_AlphaSet__list__Format
    P0_PUSCH_AlphaSet__F1 P0_PUSCH_AlphaSet__F2 P0_PUSCH_AlphaSet__F1F2_cond  P0_PUSCH_AlphaSet__F1F2_cond2 P0_PUSCH_AlphaSet__F2F1_cond.
Opaque P0_PUSCH_AlphaSet__cond P0_PUSCH_AlphaSet__Format.

