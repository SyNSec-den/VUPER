Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSSI_Range_r16.

Opaque RSSI_Range_r16__cond RSSI_Range_r16__Format.

Lemma MeasResultForRSSI_r16__channelOccupancy_r16__helper1 : (0 <= 100)%Z.  lia. Qed.
Lemma MeasResultForRSSI_r16__channelOccupancy_r16__helper2 : to_bit_sz (Z.to_nat (100 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (100 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultForRSSI_r16__channelOccupancy_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultForRSSI_r16__channelOccupancy_r16__Type := Z.
Definition MeasResultForRSSI_r16__channelOccupancy_r16__cond := (fun z => (0 <= z <= 100)%Z).
Record MeasResultForRSSI_r16__Type : Set :=
  make__MeasResultForRSSI_r16__Type {
    MeasResultForRSSI_r16__rssi_Result_r16 : RSSI_Range_r16__Type ;
    MeasResultForRSSI_r16__channelOccupancy_r16 : Z ;
}.
Definition MeasResultForRSSI_r16__list := (
 Nor RSSI_Range_r16__Type RSSI_Range_r16__cond ::
 Nor Z MeasResultForRSSI_r16__channelOccupancy_r16__cond ::
 nil).
Definition MeasResultForRSSI_r16__cond z := 
  RSSI_Range_r16__cond (MeasResultForRSSI_r16__rssi_Result_r16 z) /\
  MeasResultForRSSI_r16__channelOccupancy_r16__cond (MeasResultForRSSI_r16__channelOccupancy_r16 z) /\
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
Definition MeasResultForRSSI_r16__channelOccupancy_r16__Format : T_Format Z MeasResultForRSSI_r16__channelOccupancy_r16__cond :=
 ranged_int_format (0) (100) MeasResultForRSSI_r16__channelOccupancy_r16__helper1 MeasResultForRSSI_r16__channelOccupancy_r16__helper2.

Opaque MeasResultForRSSI_r16__channelOccupancy_r16__cond MeasResultForRSSI_r16__channelOccupancy_r16__Format.


Definition MeasResultForRSSI_r16__Format_Type := Eval cbn in seq_format_prod MeasResultForRSSI_r16__list.
Definition MeasResultForRSSI_r16__Format_list : MeasResultForRSSI_r16__Format_Type :=
  (RSSI_Range_r16__Format, (MeasResultForRSSI_r16__channelOccupancy_r16__Format, unit_format)).
Definition MeasResultForRSSI_r16__list__Format := (*Eval compute in *) seq_format MeasResultForRSSI_r16__list MeasResultForRSSI_r16__Format_list.
Definition MeasResultForRSSI_r16__F1 z :=
  (MeasResultForRSSI_r16__rssi_Result_r16 z, (MeasResultForRSSI_r16__channelOccupancy_r16 z, tt)).
Definition MeasResultForRSSI_r16__F2 (y : seq_type MeasResultForRSSI_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultForRSSI_r16__Type i0 i1
  end.
Lemma MeasResultForRSSI_r16__F1F2_cond (z : MeasResultForRSSI_r16__Type)
  : MeasResultForRSSI_r16__cond z ->
  (seq_cond MeasResultForRSSI_r16__list (MeasResultForRSSI_r16__F1 z)).
intro H. unfold MeasResultForRSSI_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultForRSSI_r16__F1F2_cond2 (z : MeasResultForRSSI_r16__Type)
 : MeasResultForRSSI_r16__F2 (MeasResultForRSSI_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultForRSSI_r16__F2F1_cond (y : seq_type MeasResultForRSSI_r16__list)
  : seq_cond MeasResultForRSSI_r16__list y ->
 (MeasResultForRSSI_r16__cond (MeasResultForRSSI_r16__F2 y)) /\  MeasResultForRSSI_r16__F1 (MeasResultForRSSI_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultForRSSI_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultForRSSI_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultForRSSI_r16__Format : T_Format MeasResultForRSSI_r16__Type MeasResultForRSSI_r16__cond :=
        proj2_format  MeasResultForRSSI_r16__cond MeasResultForRSSI_r16__list__Format
    MeasResultForRSSI_r16__F1 MeasResultForRSSI_r16__F2 MeasResultForRSSI_r16__F1F2_cond  MeasResultForRSSI_r16__F1F2_cond2 MeasResultForRSSI_r16__F2F1_cond.
Opaque MeasResultForRSSI_r16__cond MeasResultForRSSI_r16__Format.

