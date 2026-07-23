Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandCombinationList_v16a0.

Opaque BandCombinationList_v16a0__cond BandCombinationList_v16a0__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v16a0.

Opaque BandCombinationList_UplinkTxSwitch_v16a0__cond BandCombinationList_UplinkTxSwitch_v16a0__Format.

Record RF_Parameters_v16a0__Type : Set :=
  make__RF_Parameters_v16a0__Type {
    RF_Parameters_v16a0__supportedBandCombinationList_v16a0 : option BandCombinationList_v16a0__Type ;
    RF_Parameters_v16a0__supportedBandCombinationList_UplinkTxSwitch_v16a0 : option BandCombinationList_UplinkTxSwitch_v16a0__Type ;
}.
Definition RF_Parameters_v16a0__list := (
 Opt BandCombinationList_v16a0__Type BandCombinationList_v16a0__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v16a0__Type BandCombinationList_UplinkTxSwitch_v16a0__cond ::
 nil).
Definition RF_Parameters_v16a0__cond z := 
  opt_cond BandCombinationList_v16a0__cond (RF_Parameters_v16a0__supportedBandCombinationList_v16a0 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v16a0__cond (RF_Parameters_v16a0__supportedBandCombinationList_UplinkTxSwitch_v16a0 z) /\
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

Definition RF_Parameters_v16a0__Format_Type := Eval cbn in seq_format_prod RF_Parameters_v16a0__list.
Definition RF_Parameters_v16a0__Format_list : RF_Parameters_v16a0__Format_Type :=
  (BandCombinationList_v16a0__Format, (BandCombinationList_UplinkTxSwitch_v16a0__Format, unit_format)).
Definition RF_Parameters_v16a0__list__Format := (*Eval compute in *) seq_format RF_Parameters_v16a0__list RF_Parameters_v16a0__Format_list.
Definition RF_Parameters_v16a0__F1 z :=
  (RF_Parameters_v16a0__supportedBandCombinationList_v16a0 z, (RF_Parameters_v16a0__supportedBandCombinationList_UplinkTxSwitch_v16a0 z, tt)).
Definition RF_Parameters_v16a0__F2 (y : seq_type RF_Parameters_v16a0__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_Parameters_v16a0__Type i0 i1
  end.
Lemma RF_Parameters_v16a0__F1F2_cond (z : RF_Parameters_v16a0__Type)
  : RF_Parameters_v16a0__cond z ->
  (seq_cond RF_Parameters_v16a0__list (RF_Parameters_v16a0__F1 z)).
intro H. unfold RF_Parameters_v16a0__cond in H. simpl. auto. Qed.
Lemma RF_Parameters_v16a0__F1F2_cond2 (z : RF_Parameters_v16a0__Type)
 : RF_Parameters_v16a0__F2 (RF_Parameters_v16a0__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters_v16a0__F2F1_cond (y : seq_type RF_Parameters_v16a0__list)
  : seq_cond RF_Parameters_v16a0__list y ->
 (RF_Parameters_v16a0__cond (RF_Parameters_v16a0__F2 y)) /\  RF_Parameters_v16a0__F1 (RF_Parameters_v16a0__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters_v16a0__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters_v16a0__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters_v16a0__Format : T_Format RF_Parameters_v16a0__Type RF_Parameters_v16a0__cond :=
        proj2_format  RF_Parameters_v16a0__cond RF_Parameters_v16a0__list__Format
    RF_Parameters_v16a0__F1 RF_Parameters_v16a0__F2 RF_Parameters_v16a0__F1F2_cond  RF_Parameters_v16a0__F1F2_cond2 RF_Parameters_v16a0__F2F1_cond.
Opaque RF_Parameters_v16a0__cond RF_Parameters_v16a0__Format.

