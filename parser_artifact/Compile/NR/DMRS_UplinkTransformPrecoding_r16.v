Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__Type := Z.
Definition DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__cond := (fun z => (0 <= z <= 65535)%Z).
Lemma DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__Type := Z.
Definition DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__cond := (fun z => (0 <= z <= 65535)%Z).
Record DMRS_UplinkTransformPrecoding_r16__Type : Set :=
  make__DMRS_UplinkTransformPrecoding_r16__Type {
    DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0 : option Z ;
    DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1 : option Z ;
}.
Definition DMRS_UplinkTransformPrecoding_r16__list := (
 Opt Z DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__cond ::
 Opt Z DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__cond ::
 nil).
Definition DMRS_UplinkTransformPrecoding_r16__cond z := 
  opt_cond DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__cond (DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0 z) /\
  opt_cond DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__cond (DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1 z) /\
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
Definition DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__Format : T_Format Z DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__cond :=
 ranged_int_format (0) (65535) DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__helper1 DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__helper2.

Opaque DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__cond DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__Format.

Definition DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__Format : T_Format Z DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__cond :=
 ranged_int_format (0) (65535) DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__helper1 DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__helper2.

Opaque DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__cond DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__Format.


Definition DMRS_UplinkTransformPrecoding_r16__Format_Type := Eval cbn in seq_format_prod DMRS_UplinkTransformPrecoding_r16__list.
Definition DMRS_UplinkTransformPrecoding_r16__Format_list : DMRS_UplinkTransformPrecoding_r16__Format_Type :=
  (DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0__Format, (DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1__Format, unit_format)).
Definition DMRS_UplinkTransformPrecoding_r16__list__Format := (*Eval compute in *) seq_format DMRS_UplinkTransformPrecoding_r16__list DMRS_UplinkTransformPrecoding_r16__Format_list.
Definition DMRS_UplinkTransformPrecoding_r16__F1 z :=
  (DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID0 z, (DMRS_UplinkTransformPrecoding_r16__pi2BPSK_ScramblingID1 z, tt)).
Definition DMRS_UplinkTransformPrecoding_r16__F2 (y : seq_type DMRS_UplinkTransformPrecoding_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DMRS_UplinkTransformPrecoding_r16__Type i0 i1
  end.
Lemma DMRS_UplinkTransformPrecoding_r16__F1F2_cond (z : DMRS_UplinkTransformPrecoding_r16__Type)
  : DMRS_UplinkTransformPrecoding_r16__cond z ->
  (seq_cond DMRS_UplinkTransformPrecoding_r16__list (DMRS_UplinkTransformPrecoding_r16__F1 z)).
intro H. unfold DMRS_UplinkTransformPrecoding_r16__cond in H. simpl. auto. Qed.
Lemma DMRS_UplinkTransformPrecoding_r16__F1F2_cond2 (z : DMRS_UplinkTransformPrecoding_r16__Type)
 : DMRS_UplinkTransformPrecoding_r16__F2 (DMRS_UplinkTransformPrecoding_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DMRS_UplinkTransformPrecoding_r16__F2F1_cond (y : seq_type DMRS_UplinkTransformPrecoding_r16__list)
  : seq_cond DMRS_UplinkTransformPrecoding_r16__list y ->
 (DMRS_UplinkTransformPrecoding_r16__cond (DMRS_UplinkTransformPrecoding_r16__F2 y)) /\  DMRS_UplinkTransformPrecoding_r16__F1 (DMRS_UplinkTransformPrecoding_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DMRS_UplinkTransformPrecoding_r16__cond. simpl in *. auto.
 - simpl. unfold DMRS_UplinkTransformPrecoding_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DMRS_UplinkTransformPrecoding_r16__Format : T_Format DMRS_UplinkTransformPrecoding_r16__Type DMRS_UplinkTransformPrecoding_r16__cond :=
        proj2_format  DMRS_UplinkTransformPrecoding_r16__cond DMRS_UplinkTransformPrecoding_r16__list__Format
    DMRS_UplinkTransformPrecoding_r16__F1 DMRS_UplinkTransformPrecoding_r16__F2 DMRS_UplinkTransformPrecoding_r16__F1F2_cond  DMRS_UplinkTransformPrecoding_r16__F1F2_cond2 DMRS_UplinkTransformPrecoding_r16__F2F1_cond.
Opaque DMRS_UplinkTransformPrecoding_r16__cond DMRS_UplinkTransformPrecoding_r16__Format.

