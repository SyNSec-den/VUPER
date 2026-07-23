Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Lemma SPS_PUCCH_AN_r16__maxPayloadSize_r16__helper1 : (4 <= 256)%Z.  lia. Qed.
Lemma SPS_PUCCH_AN_r16__maxPayloadSize_r16__helper2 : to_bit_sz (Z.to_nat (256 - 4)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 4))%Z). { apply Zorder.Zle_minus_le_0. apply SPS_PUCCH_AN_r16__maxPayloadSize_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SPS_PUCCH_AN_r16__maxPayloadSize_r16__Type := Z.
Definition SPS_PUCCH_AN_r16__maxPayloadSize_r16__cond := (fun z => (4 <= z <= 256)%Z).
Record SPS_PUCCH_AN_r16__Type : Set :=
  make__SPS_PUCCH_AN_r16__Type {
    SPS_PUCCH_AN_r16__sps_PUCCH_AN_ResourceID_r16 : PUCCH_ResourceId__Type ;
    SPS_PUCCH_AN_r16__maxPayloadSize_r16 : option Z ;
}.
Definition SPS_PUCCH_AN_r16__list := (
 Nor PUCCH_ResourceId__Type PUCCH_ResourceId__cond ::
 Opt Z SPS_PUCCH_AN_r16__maxPayloadSize_r16__cond ::
 nil).
Definition SPS_PUCCH_AN_r16__cond z := 
  PUCCH_ResourceId__cond (SPS_PUCCH_AN_r16__sps_PUCCH_AN_ResourceID_r16 z) /\
  opt_cond SPS_PUCCH_AN_r16__maxPayloadSize_r16__cond (SPS_PUCCH_AN_r16__maxPayloadSize_r16 z) /\
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
Definition SPS_PUCCH_AN_r16__maxPayloadSize_r16__Format : T_Format Z SPS_PUCCH_AN_r16__maxPayloadSize_r16__cond :=
 ranged_int_format (4) (256) SPS_PUCCH_AN_r16__maxPayloadSize_r16__helper1 SPS_PUCCH_AN_r16__maxPayloadSize_r16__helper2.

Opaque SPS_PUCCH_AN_r16__maxPayloadSize_r16__cond SPS_PUCCH_AN_r16__maxPayloadSize_r16__Format.


Definition SPS_PUCCH_AN_r16__Format_Type := Eval cbn in seq_format_prod SPS_PUCCH_AN_r16__list.
Definition SPS_PUCCH_AN_r16__Format_list : SPS_PUCCH_AN_r16__Format_Type :=
  (PUCCH_ResourceId__Format, (SPS_PUCCH_AN_r16__maxPayloadSize_r16__Format, unit_format)).
Definition SPS_PUCCH_AN_r16__list__Format := (*Eval compute in *) seq_format SPS_PUCCH_AN_r16__list SPS_PUCCH_AN_r16__Format_list.
Definition SPS_PUCCH_AN_r16__F1 z :=
  (SPS_PUCCH_AN_r16__sps_PUCCH_AN_ResourceID_r16 z, (SPS_PUCCH_AN_r16__maxPayloadSize_r16 z, tt)).
Definition SPS_PUCCH_AN_r16__F2 (y : seq_type SPS_PUCCH_AN_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SPS_PUCCH_AN_r16__Type i0 i1
  end.
Lemma SPS_PUCCH_AN_r16__F1F2_cond (z : SPS_PUCCH_AN_r16__Type)
  : SPS_PUCCH_AN_r16__cond z ->
  (seq_cond SPS_PUCCH_AN_r16__list (SPS_PUCCH_AN_r16__F1 z)).
intro H. unfold SPS_PUCCH_AN_r16__cond in H. simpl. auto. Qed.
Lemma SPS_PUCCH_AN_r16__F1F2_cond2 (z : SPS_PUCCH_AN_r16__Type)
 : SPS_PUCCH_AN_r16__F2 (SPS_PUCCH_AN_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SPS_PUCCH_AN_r16__F2F1_cond (y : seq_type SPS_PUCCH_AN_r16__list)
  : seq_cond SPS_PUCCH_AN_r16__list y ->
 (SPS_PUCCH_AN_r16__cond (SPS_PUCCH_AN_r16__F2 y)) /\  SPS_PUCCH_AN_r16__F1 (SPS_PUCCH_AN_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SPS_PUCCH_AN_r16__cond. simpl in *. auto.
 - simpl. unfold SPS_PUCCH_AN_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SPS_PUCCH_AN_r16__Format : T_Format SPS_PUCCH_AN_r16__Type SPS_PUCCH_AN_r16__cond :=
        proj2_format  SPS_PUCCH_AN_r16__cond SPS_PUCCH_AN_r16__list__Format
    SPS_PUCCH_AN_r16__F1 SPS_PUCCH_AN_r16__F2 SPS_PUCCH_AN_r16__F1F2_cond  SPS_PUCCH_AN_r16__F1F2_cond2 SPS_PUCCH_AN_r16__F2F1_cond.
Opaque SPS_PUCCH_AN_r16__cond SPS_PUCCH_AN_r16__Format.

