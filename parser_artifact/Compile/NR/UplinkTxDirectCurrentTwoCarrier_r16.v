Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UplinkTxDirectCurrentCarrierInfo_r16.

Opaque UplinkTxDirectCurrentCarrierInfo_r16__cond UplinkTxDirectCurrentCarrierInfo_r16__Format.

Require Import NR.UplinkTxDirectCurrentCarrierInfo_r16.

Opaque UplinkTxDirectCurrentCarrierInfo_r16__cond UplinkTxDirectCurrentCarrierInfo_r16__Format.

Require Import NR.UplinkTxDirectCurrentTwoCarrierInfo_r16.

Opaque UplinkTxDirectCurrentTwoCarrierInfo_r16__cond UplinkTxDirectCurrentTwoCarrierInfo_r16__Format.

Require Import NR.UplinkTxDirectCurrentTwoCarrierInfo_r16.

Opaque UplinkTxDirectCurrentTwoCarrierInfo_r16__cond UplinkTxDirectCurrentTwoCarrierInfo_r16__Format.

Record UplinkTxDirectCurrentTwoCarrier_r16__Type : Set :=
  make__UplinkTxDirectCurrentTwoCarrier_r16__Type {
    UplinkTxDirectCurrentTwoCarrier_r16__carrierOneInfo_r16 : UplinkTxDirectCurrentCarrierInfo_r16__Type ;
    UplinkTxDirectCurrentTwoCarrier_r16__carrierTwoInfo_r16 : UplinkTxDirectCurrentCarrierInfo_r16__Type ;
    UplinkTxDirectCurrentTwoCarrier_r16__singlePA_TxDirectCurrent_r16 : UplinkTxDirectCurrentTwoCarrierInfo_r16__Type ;
    UplinkTxDirectCurrentTwoCarrier_r16__secondPA_TxDirectCurrent_r16 : option UplinkTxDirectCurrentTwoCarrierInfo_r16__Type ;
}.
Definition UplinkTxDirectCurrentTwoCarrier_r16__list := (
 Nor UplinkTxDirectCurrentCarrierInfo_r16__Type UplinkTxDirectCurrentCarrierInfo_r16__cond ::
 Nor UplinkTxDirectCurrentCarrierInfo_r16__Type UplinkTxDirectCurrentCarrierInfo_r16__cond ::
 Nor UplinkTxDirectCurrentTwoCarrierInfo_r16__Type UplinkTxDirectCurrentTwoCarrierInfo_r16__cond ::
 Opt UplinkTxDirectCurrentTwoCarrierInfo_r16__Type UplinkTxDirectCurrentTwoCarrierInfo_r16__cond ::
 nil).
Definition UplinkTxDirectCurrentTwoCarrier_r16__cond z := 
  UplinkTxDirectCurrentCarrierInfo_r16__cond (UplinkTxDirectCurrentTwoCarrier_r16__carrierOneInfo_r16 z) /\
  UplinkTxDirectCurrentCarrierInfo_r16__cond (UplinkTxDirectCurrentTwoCarrier_r16__carrierTwoInfo_r16 z) /\
  UplinkTxDirectCurrentTwoCarrierInfo_r16__cond (UplinkTxDirectCurrentTwoCarrier_r16__singlePA_TxDirectCurrent_r16 z) /\
  opt_cond UplinkTxDirectCurrentTwoCarrierInfo_r16__cond (UplinkTxDirectCurrentTwoCarrier_r16__secondPA_TxDirectCurrent_r16 z) /\
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

Definition UplinkTxDirectCurrentTwoCarrier_r16__Format_Type := Eval cbn in seq_format_prod UplinkTxDirectCurrentTwoCarrier_r16__list.
Definition UplinkTxDirectCurrentTwoCarrier_r16__Format_list : UplinkTxDirectCurrentTwoCarrier_r16__Format_Type :=
  (UplinkTxDirectCurrentCarrierInfo_r16__Format, (UplinkTxDirectCurrentCarrierInfo_r16__Format, (UplinkTxDirectCurrentTwoCarrierInfo_r16__Format, (UplinkTxDirectCurrentTwoCarrierInfo_r16__Format, unit_format)))).
Definition UplinkTxDirectCurrentTwoCarrier_r16__list__Format := (*Eval compute in *) seq_format UplinkTxDirectCurrentTwoCarrier_r16__list UplinkTxDirectCurrentTwoCarrier_r16__Format_list.
Definition UplinkTxDirectCurrentTwoCarrier_r16__F1 z :=
  (UplinkTxDirectCurrentTwoCarrier_r16__carrierOneInfo_r16 z, (UplinkTxDirectCurrentTwoCarrier_r16__carrierTwoInfo_r16 z, (UplinkTxDirectCurrentTwoCarrier_r16__singlePA_TxDirectCurrent_r16 z, (UplinkTxDirectCurrentTwoCarrier_r16__secondPA_TxDirectCurrent_r16 z, tt)))).
Definition UplinkTxDirectCurrentTwoCarrier_r16__F2 (y : seq_type UplinkTxDirectCurrentTwoCarrier_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__UplinkTxDirectCurrentTwoCarrier_r16__Type i0 i1 i2 i3
  end.
Lemma UplinkTxDirectCurrentTwoCarrier_r16__F1F2_cond (z : UplinkTxDirectCurrentTwoCarrier_r16__Type)
  : UplinkTxDirectCurrentTwoCarrier_r16__cond z ->
  (seq_cond UplinkTxDirectCurrentTwoCarrier_r16__list (UplinkTxDirectCurrentTwoCarrier_r16__F1 z)).
intro H. unfold UplinkTxDirectCurrentTwoCarrier_r16__cond in H. simpl. auto. Qed.
Lemma UplinkTxDirectCurrentTwoCarrier_r16__F1F2_cond2 (z : UplinkTxDirectCurrentTwoCarrier_r16__Type)
 : UplinkTxDirectCurrentTwoCarrier_r16__F2 (UplinkTxDirectCurrentTwoCarrier_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkTxDirectCurrentTwoCarrier_r16__F2F1_cond (y : seq_type UplinkTxDirectCurrentTwoCarrier_r16__list)
  : seq_cond UplinkTxDirectCurrentTwoCarrier_r16__list y ->
 (UplinkTxDirectCurrentTwoCarrier_r16__cond (UplinkTxDirectCurrentTwoCarrier_r16__F2 y)) /\  UplinkTxDirectCurrentTwoCarrier_r16__F1 (UplinkTxDirectCurrentTwoCarrier_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkTxDirectCurrentTwoCarrier_r16__cond. simpl in *. auto.
 - simpl. unfold UplinkTxDirectCurrentTwoCarrier_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkTxDirectCurrentTwoCarrier_r16__Format : T_Format UplinkTxDirectCurrentTwoCarrier_r16__Type UplinkTxDirectCurrentTwoCarrier_r16__cond :=
        proj2_format  UplinkTxDirectCurrentTwoCarrier_r16__cond UplinkTxDirectCurrentTwoCarrier_r16__list__Format
    UplinkTxDirectCurrentTwoCarrier_r16__F1 UplinkTxDirectCurrentTwoCarrier_r16__F2 UplinkTxDirectCurrentTwoCarrier_r16__F1F2_cond  UplinkTxDirectCurrentTwoCarrier_r16__F1F2_cond2 UplinkTxDirectCurrentTwoCarrier_r16__F2F1_cond.
Opaque UplinkTxDirectCurrentTwoCarrier_r16__cond UplinkTxDirectCurrentTwoCarrier_r16__Format.

