Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_RS_Index.

Opaque CSI_RS_Index__cond CSI_RS_Index__Format.

Lemma PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__helper1 : (1 <= 200)%Z.  lia. Qed.
Lemma PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__helper2 : to_bit_sz (Z.to_nat (200 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (200 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__Type := Z.
Definition PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__cond := (fun z => (1 <= z <= 200)%Z).
Record PerRACSI_RSInfo_r16__Type : Set :=
  make__PerRACSI_RSInfo_r16__Type {
    PerRACSI_RSInfo_r16__csi_RS_Index_r16 : CSI_RS_Index__Type ;
    PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16 : Z ;
}.
Definition PerRACSI_RSInfo_r16__list := (
 Nor CSI_RS_Index__Type CSI_RS_Index__cond ::
 Nor Z PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__cond ::
 nil).
Definition PerRACSI_RSInfo_r16__cond z := 
  CSI_RS_Index__cond (PerRACSI_RSInfo_r16__csi_RS_Index_r16 z) /\
  PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__cond (PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16 z) /\
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
Definition PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__Format : T_Format Z PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__cond :=
 ranged_int_format (1) (200) PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__helper1 PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__helper2.

Opaque PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__cond PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__Format.


Definition PerRACSI_RSInfo_r16__Format_Type := Eval cbn in seq_format_prod PerRACSI_RSInfo_r16__list.
Definition PerRACSI_RSInfo_r16__Format_list : PerRACSI_RSInfo_r16__Format_Type :=
  (CSI_RS_Index__Format, (PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16__Format, unit_format)).
Definition PerRACSI_RSInfo_r16__list__Format := (*Eval compute in *) seq_format PerRACSI_RSInfo_r16__list PerRACSI_RSInfo_r16__Format_list.
Definition PerRACSI_RSInfo_r16__F1 z :=
  (PerRACSI_RSInfo_r16__csi_RS_Index_r16 z, (PerRACSI_RSInfo_r16__numberOfPreamblesSentOnCSI_RS_r16 z, tt)).
Definition PerRACSI_RSInfo_r16__F2 (y : seq_type PerRACSI_RSInfo_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PerRACSI_RSInfo_r16__Type i0 i1
  end.
Lemma PerRACSI_RSInfo_r16__F1F2_cond (z : PerRACSI_RSInfo_r16__Type)
  : PerRACSI_RSInfo_r16__cond z ->
  (seq_cond PerRACSI_RSInfo_r16__list (PerRACSI_RSInfo_r16__F1 z)).
intro H. unfold PerRACSI_RSInfo_r16__cond in H. simpl. auto. Qed.
Lemma PerRACSI_RSInfo_r16__F1F2_cond2 (z : PerRACSI_RSInfo_r16__Type)
 : PerRACSI_RSInfo_r16__F2 (PerRACSI_RSInfo_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PerRACSI_RSInfo_r16__F2F1_cond (y : seq_type PerRACSI_RSInfo_r16__list)
  : seq_cond PerRACSI_RSInfo_r16__list y ->
 (PerRACSI_RSInfo_r16__cond (PerRACSI_RSInfo_r16__F2 y)) /\  PerRACSI_RSInfo_r16__F1 (PerRACSI_RSInfo_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PerRACSI_RSInfo_r16__cond. simpl in *. auto.
 - simpl. unfold PerRACSI_RSInfo_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PerRACSI_RSInfo_r16__Format : T_Format PerRACSI_RSInfo_r16__Type PerRACSI_RSInfo_r16__cond :=
        proj2_format  PerRACSI_RSInfo_r16__cond PerRACSI_RSInfo_r16__list__Format
    PerRACSI_RSInfo_r16__F1 PerRACSI_RSInfo_r16__F2 PerRACSI_RSInfo_r16__F1F2_cond  PerRACSI_RSInfo_r16__F1F2_cond2 PerRACSI_RSInfo_r16__F2F1_cond.
Opaque PerRACSI_RSInfo_r16__cond PerRACSI_RSInfo_r16__Format.

