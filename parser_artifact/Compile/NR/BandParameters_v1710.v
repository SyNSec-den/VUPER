Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__Type := bit_string_fixed.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 11 /\ bit_string_len_prop (fst z) (snd z)).
Lemma BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__Type := Z.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__cond := (fun z => (1 <= z <= 32)%Z).
Lemma BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__Type := Z.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__cond := (fun z => (1 <= z <= 32)%Z).
Record BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Type : Set :=
  make__BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Type {
    BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17 : BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__Type ;
    BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17 : option Z ;
    BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17 : option Z ;
}.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list := (
 Nor BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__Type BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__cond ::
 Opt Z BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__cond ::
 Opt Z BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__cond ::
 nil).
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond z := 
  BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__cond (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17 z) /\
  opt_cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__cond (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17 z) /\
  opt_cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__cond (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17 z) /\
  True.

Record BandParameters_v1710__Type : Set :=
  make__BandParameters_v1710__Type {
    BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17 : option BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Type ;
}.
Definition BandParameters_v1710__list := (
 Opt BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Type BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond ::
 nil).
Definition BandParameters_v1710__cond z := 
  opt_cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17 z) /\
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
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__Format : T_Format BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__Type BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__cond := (* Eval compute in *) bit_string_fixed_format 11.
Opaque BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__Format.

Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__Format : T_Format Z BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__cond :=
 ranged_int_format (1) (32) BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__helper1 BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__helper2.

Opaque BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__Format.

Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__Format : T_Format Z BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__cond :=
 ranged_int_format (1) (32) BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__helper1 BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__helper2.

Opaque BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__Format.


Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Format_Type := Eval cbn in seq_format_prod BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Format_list : BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Format_Type :=
  (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17__Format, (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17__Format, (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17__Format, unit_format))).
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list__Format := (*Eval compute in *) seq_format BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Format_list.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1 z :=
  (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__supportedSRS_TxPortSwitchBeyond4Rx_r17 z, (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberAffectBeyond4Rx_r17 z, (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__entryNumberSwitchBeyond4Rx_r17 z, tt))).
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F2 (y : seq_type BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Type i0 i1 i2
  end.
Lemma BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1F2_cond (z : BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Type)
  : BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond z ->
  (seq_cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1 z)).
intro H. unfold BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond in H. simpl. auto. Qed.
Lemma BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1F2_cond2 (z : BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Type)
 : BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F2 (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F2F1_cond (y : seq_type BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list)
  : seq_cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list y ->
 (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F2 y)) /\  BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1 (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond. simpl in *. auto.
 - simpl. unfold BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Format : T_Format BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Type BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond :=
        proj2_format  BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__list__Format
    BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1 BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F2 BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1F2_cond  BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F1F2_cond2 BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__F2F1_cond.
Opaque BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__cond BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Format.


Definition BandParameters_v1710__Format_Type := Eval cbn in seq_format_prod BandParameters_v1710__list.
Definition BandParameters_v1710__Format_list : BandParameters_v1710__Format_Type :=
  (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17__Format, unit_format).
Definition BandParameters_v1710__list__Format := (*Eval compute in *) seq_format BandParameters_v1710__list BandParameters_v1710__Format_list.
Definition BandParameters_v1710__F1 z :=
  (BandParameters_v1710__srs_AntennaSwitchingBeyond4RX_r17 z, tt).
Definition BandParameters_v1710__F2 (y : seq_type BandParameters_v1710__list) :=
  match y with
  | (i0, _)=>
    make__BandParameters_v1710__Type i0
  end.
Lemma BandParameters_v1710__F1F2_cond (z : BandParameters_v1710__Type)
  : BandParameters_v1710__cond z ->
  (seq_cond BandParameters_v1710__list (BandParameters_v1710__F1 z)).
intro H. unfold BandParameters_v1710__cond in H. simpl. auto. Qed.
Lemma BandParameters_v1710__F1F2_cond2 (z : BandParameters_v1710__Type)
 : BandParameters_v1710__F2 (BandParameters_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters_v1710__F2F1_cond (y : seq_type BandParameters_v1710__list)
  : seq_cond BandParameters_v1710__list y ->
 (BandParameters_v1710__cond (BandParameters_v1710__F2 y)) /\  BandParameters_v1710__F1 (BandParameters_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters_v1710__cond. simpl in *. auto.
 - simpl. unfold BandParameters_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters_v1710__Format : T_Format BandParameters_v1710__Type BandParameters_v1710__cond :=
        proj2_format  BandParameters_v1710__cond BandParameters_v1710__list__Format
    BandParameters_v1710__F1 BandParameters_v1710__F2 BandParameters_v1710__F1F2_cond  BandParameters_v1710__F1F2_cond2 BandParameters_v1710__F2F1_cond.
Opaque BandParameters_v1710__cond BandParameters_v1710__Format.

