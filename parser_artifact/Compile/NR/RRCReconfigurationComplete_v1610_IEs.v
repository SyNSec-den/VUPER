Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UE_MeasurementsAvailable_r16.

Opaque UE_MeasurementsAvailable_r16__cond UE_MeasurementsAvailable_r16__Format.

Require Import NR.NeedForGapsInfoNR_r16.

Opaque NeedForGapsInfoNR_r16__cond NeedForGapsInfoNR_r16__Format.

Require Import NR.RRCReconfigurationComplete_v1640_IEs.

Opaque RRCReconfigurationComplete_v1640_IEs__cond RRCReconfigurationComplete_v1640_IEs__Format.

Record RRCReconfigurationComplete_v1610_IEs__Type : Set :=
  make__RRCReconfigurationComplete_v1610_IEs__Type {
    RRCReconfigurationComplete_v1610_IEs__ue_MeasurementsAvailable_r16 : option UE_MeasurementsAvailable_r16__Type ;
    RRCReconfigurationComplete_v1610_IEs__needForGapsInfoNR_r16 : option NeedForGapsInfoNR_r16__Type ;
    RRCReconfigurationComplete_v1610_IEs__nonCriticalExtension : option RRCReconfigurationComplete_v1640_IEs__Type ;
}.
Definition RRCReconfigurationComplete_v1610_IEs__list := (
 Opt UE_MeasurementsAvailable_r16__Type UE_MeasurementsAvailable_r16__cond ::
 Opt NeedForGapsInfoNR_r16__Type NeedForGapsInfoNR_r16__cond ::
 Opt RRCReconfigurationComplete_v1640_IEs__Type RRCReconfigurationComplete_v1640_IEs__cond ::
 nil).
Definition RRCReconfigurationComplete_v1610_IEs__cond z := 
  opt_cond UE_MeasurementsAvailable_r16__cond (RRCReconfigurationComplete_v1610_IEs__ue_MeasurementsAvailable_r16 z) /\
  opt_cond NeedForGapsInfoNR_r16__cond (RRCReconfigurationComplete_v1610_IEs__needForGapsInfoNR_r16 z) /\
  opt_cond RRCReconfigurationComplete_v1640_IEs__cond (RRCReconfigurationComplete_v1610_IEs__nonCriticalExtension z) /\
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

Definition RRCReconfigurationComplete_v1610_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationComplete_v1610_IEs__list.
Definition RRCReconfigurationComplete_v1610_IEs__Format_list : RRCReconfigurationComplete_v1610_IEs__Format_Type :=
  (UE_MeasurementsAvailable_r16__Format, (NeedForGapsInfoNR_r16__Format, (RRCReconfigurationComplete_v1640_IEs__Format, unit_format))).
Definition RRCReconfigurationComplete_v1610_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfigurationComplete_v1610_IEs__list RRCReconfigurationComplete_v1610_IEs__Format_list.
Definition RRCReconfigurationComplete_v1610_IEs__F1 z :=
  (RRCReconfigurationComplete_v1610_IEs__ue_MeasurementsAvailable_r16 z, (RRCReconfigurationComplete_v1610_IEs__needForGapsInfoNR_r16 z, (RRCReconfigurationComplete_v1610_IEs__nonCriticalExtension z, tt))).
Definition RRCReconfigurationComplete_v1610_IEs__F2 (y : seq_type RRCReconfigurationComplete_v1610_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RRCReconfigurationComplete_v1610_IEs__Type i0 i1 i2
  end.
Lemma RRCReconfigurationComplete_v1610_IEs__F1F2_cond (z : RRCReconfigurationComplete_v1610_IEs__Type)
  : RRCReconfigurationComplete_v1610_IEs__cond z ->
  (seq_cond RRCReconfigurationComplete_v1610_IEs__list (RRCReconfigurationComplete_v1610_IEs__F1 z)).
intro H. unfold RRCReconfigurationComplete_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationComplete_v1610_IEs__F1F2_cond2 (z : RRCReconfigurationComplete_v1610_IEs__Type)
 : RRCReconfigurationComplete_v1610_IEs__F2 (RRCReconfigurationComplete_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationComplete_v1610_IEs__F2F1_cond (y : seq_type RRCReconfigurationComplete_v1610_IEs__list)
  : seq_cond RRCReconfigurationComplete_v1610_IEs__list y ->
 (RRCReconfigurationComplete_v1610_IEs__cond (RRCReconfigurationComplete_v1610_IEs__F2 y)) /\  RRCReconfigurationComplete_v1610_IEs__F1 (RRCReconfigurationComplete_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationComplete_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationComplete_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationComplete_v1610_IEs__Format : T_Format RRCReconfigurationComplete_v1610_IEs__Type RRCReconfigurationComplete_v1610_IEs__cond :=
        proj2_format  RRCReconfigurationComplete_v1610_IEs__cond RRCReconfigurationComplete_v1610_IEs__list__Format
    RRCReconfigurationComplete_v1610_IEs__F1 RRCReconfigurationComplete_v1610_IEs__F2 RRCReconfigurationComplete_v1610_IEs__F1F2_cond  RRCReconfigurationComplete_v1610_IEs__F1F2_cond2 RRCReconfigurationComplete_v1610_IEs__F2F1_cond.
Opaque RRCReconfigurationComplete_v1610_IEs__cond RRCReconfigurationComplete_v1610_IEs__Format.

