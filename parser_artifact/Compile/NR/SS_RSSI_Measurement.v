Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SS_RSSI_Measurement__measurementSlots__helper1 : (0 <= 1 <= 80)%Z.  lia. Qed.
Lemma SS_RSSI_Measurement__measurementSlots__helper2 : to_bit_sz (Z.to_nat (80 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (80 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SS_RSSI_Measurement__measurementSlots__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SS_RSSI_Measurement__measurementSlots__Type := bit_string.
Definition SS_RSSI_Measurement__measurementSlots__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 80)%Z /\ bit_string_len_prop (fst z) (snd z)).
Lemma SS_RSSI_Measurement__endSymbol__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SS_RSSI_Measurement__endSymbol__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SS_RSSI_Measurement__endSymbol__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SS_RSSI_Measurement__endSymbol__Type := Z.
Definition SS_RSSI_Measurement__endSymbol__cond := (fun z => (0 <= z <= 3)%Z).
Record SS_RSSI_Measurement__Type : Set :=
  make__SS_RSSI_Measurement__Type {
    SS_RSSI_Measurement__measurementSlots : SS_RSSI_Measurement__measurementSlots__Type ;
    SS_RSSI_Measurement__endSymbol : Z ;
}.
Definition SS_RSSI_Measurement__list := (
 Nor SS_RSSI_Measurement__measurementSlots__Type SS_RSSI_Measurement__measurementSlots__cond ::
 Nor Z SS_RSSI_Measurement__endSymbol__cond ::
 nil).
Definition SS_RSSI_Measurement__cond z := 
  SS_RSSI_Measurement__measurementSlots__cond (SS_RSSI_Measurement__measurementSlots z) /\
  SS_RSSI_Measurement__endSymbol__cond (SS_RSSI_Measurement__endSymbol z) /\
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
Definition SS_RSSI_Measurement__measurementSlots__Format : T_Format SS_RSSI_Measurement__measurementSlots__Type SS_RSSI_Measurement__measurementSlots__cond := (* Eval compute in *) bit_string_ranged_format 1 80 SS_RSSI_Measurement__measurementSlots__helper1 SS_RSSI_Measurement__measurementSlots__helper2.
Opaque SS_RSSI_Measurement__measurementSlots__cond SS_RSSI_Measurement__measurementSlots__Format.

Definition SS_RSSI_Measurement__endSymbol__Format : T_Format Z SS_RSSI_Measurement__endSymbol__cond :=
 ranged_int_format (0) (3) SS_RSSI_Measurement__endSymbol__helper1 SS_RSSI_Measurement__endSymbol__helper2.

Opaque SS_RSSI_Measurement__endSymbol__cond SS_RSSI_Measurement__endSymbol__Format.


Definition SS_RSSI_Measurement__Format_Type := Eval cbn in seq_format_prod SS_RSSI_Measurement__list.
Definition SS_RSSI_Measurement__Format_list : SS_RSSI_Measurement__Format_Type :=
  (SS_RSSI_Measurement__measurementSlots__Format, (SS_RSSI_Measurement__endSymbol__Format, unit_format)).
Definition SS_RSSI_Measurement__list__Format := (*Eval compute in *) seq_format SS_RSSI_Measurement__list SS_RSSI_Measurement__Format_list.
Definition SS_RSSI_Measurement__F1 z :=
  (SS_RSSI_Measurement__measurementSlots z, (SS_RSSI_Measurement__endSymbol z, tt)).
Definition SS_RSSI_Measurement__F2 (y : seq_type SS_RSSI_Measurement__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SS_RSSI_Measurement__Type i0 i1
  end.
Lemma SS_RSSI_Measurement__F1F2_cond (z : SS_RSSI_Measurement__Type)
  : SS_RSSI_Measurement__cond z ->
  (seq_cond SS_RSSI_Measurement__list (SS_RSSI_Measurement__F1 z)).
intro H. unfold SS_RSSI_Measurement__cond in H. simpl. auto. Qed.
Lemma SS_RSSI_Measurement__F1F2_cond2 (z : SS_RSSI_Measurement__Type)
 : SS_RSSI_Measurement__F2 (SS_RSSI_Measurement__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SS_RSSI_Measurement__F2F1_cond (y : seq_type SS_RSSI_Measurement__list)
  : seq_cond SS_RSSI_Measurement__list y ->
 (SS_RSSI_Measurement__cond (SS_RSSI_Measurement__F2 y)) /\  SS_RSSI_Measurement__F1 (SS_RSSI_Measurement__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SS_RSSI_Measurement__cond. simpl in *. auto.
 - simpl. unfold SS_RSSI_Measurement__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SS_RSSI_Measurement__Format : T_Format SS_RSSI_Measurement__Type SS_RSSI_Measurement__cond :=
        proj2_format  SS_RSSI_Measurement__cond SS_RSSI_Measurement__list__Format
    SS_RSSI_Measurement__F1 SS_RSSI_Measurement__F2 SS_RSSI_Measurement__F1F2_cond  SS_RSSI_Measurement__F1F2_cond2 SS_RSSI_Measurement__F2F1_cond.
Opaque SS_RSSI_Measurement__cond SS_RSSI_Measurement__Format.

