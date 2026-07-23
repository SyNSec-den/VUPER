Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__Type := bit_string_fixed.
Definition RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat maxSI_Message /\ bit_string_len_prop (fst z) (snd z)).
Definition RRC_PosSystemInfoRequest_r16_IEs__spare__Type := bit_string_fixed.
Definition RRC_PosSystemInfoRequest_r16_IEs__spare__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 11 /\ bit_string_len_prop (fst z) (snd z)).
Record RRC_PosSystemInfoRequest_r16_IEs__Type : Set :=
  make__RRC_PosSystemInfoRequest_r16_IEs__Type {
    RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List : RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__Type ;
    RRC_PosSystemInfoRequest_r16_IEs__spare : RRC_PosSystemInfoRequest_r16_IEs__spare__Type ;
}.
Definition RRC_PosSystemInfoRequest_r16_IEs__list := (
 Nor RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__Type RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__cond ::
 Nor RRC_PosSystemInfoRequest_r16_IEs__spare__Type RRC_PosSystemInfoRequest_r16_IEs__spare__cond ::
 nil).
Definition RRC_PosSystemInfoRequest_r16_IEs__cond z := 
  RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__cond (RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List z) /\
  RRC_PosSystemInfoRequest_r16_IEs__spare__cond (RRC_PosSystemInfoRequest_r16_IEs__spare z) /\
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
Definition RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__Format : T_Format RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__Type RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__cond := (* Eval compute in *) bit_string_fixed_format maxSI_Message.
Opaque RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__cond RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__Format.

Definition RRC_PosSystemInfoRequest_r16_IEs__spare__Format : T_Format RRC_PosSystemInfoRequest_r16_IEs__spare__Type RRC_PosSystemInfoRequest_r16_IEs__spare__cond := (* Eval compute in *) bit_string_fixed_format 11.
Opaque RRC_PosSystemInfoRequest_r16_IEs__spare__cond RRC_PosSystemInfoRequest_r16_IEs__spare__Format.


Definition RRC_PosSystemInfoRequest_r16_IEs__Format_Type := Eval cbn in seq_format_prod RRC_PosSystemInfoRequest_r16_IEs__list.
Definition RRC_PosSystemInfoRequest_r16_IEs__Format_list : RRC_PosSystemInfoRequest_r16_IEs__Format_Type :=
  (RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List__Format, (RRC_PosSystemInfoRequest_r16_IEs__spare__Format, unit_format)).
Definition RRC_PosSystemInfoRequest_r16_IEs__list__Format := (*Eval compute in *) seq_format RRC_PosSystemInfoRequest_r16_IEs__list RRC_PosSystemInfoRequest_r16_IEs__Format_list.
Definition RRC_PosSystemInfoRequest_r16_IEs__F1 z :=
  (RRC_PosSystemInfoRequest_r16_IEs__requestedPosSI_List z, (RRC_PosSystemInfoRequest_r16_IEs__spare z, tt)).
Definition RRC_PosSystemInfoRequest_r16_IEs__F2 (y : seq_type RRC_PosSystemInfoRequest_r16_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRC_PosSystemInfoRequest_r16_IEs__Type i0 i1
  end.
Lemma RRC_PosSystemInfoRequest_r16_IEs__F1F2_cond (z : RRC_PosSystemInfoRequest_r16_IEs__Type)
  : RRC_PosSystemInfoRequest_r16_IEs__cond z ->
  (seq_cond RRC_PosSystemInfoRequest_r16_IEs__list (RRC_PosSystemInfoRequest_r16_IEs__F1 z)).
intro H. unfold RRC_PosSystemInfoRequest_r16_IEs__cond in H. simpl. auto. Qed.
Lemma RRC_PosSystemInfoRequest_r16_IEs__F1F2_cond2 (z : RRC_PosSystemInfoRequest_r16_IEs__Type)
 : RRC_PosSystemInfoRequest_r16_IEs__F2 (RRC_PosSystemInfoRequest_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRC_PosSystemInfoRequest_r16_IEs__F2F1_cond (y : seq_type RRC_PosSystemInfoRequest_r16_IEs__list)
  : seq_cond RRC_PosSystemInfoRequest_r16_IEs__list y ->
 (RRC_PosSystemInfoRequest_r16_IEs__cond (RRC_PosSystemInfoRequest_r16_IEs__F2 y)) /\  RRC_PosSystemInfoRequest_r16_IEs__F1 (RRC_PosSystemInfoRequest_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRC_PosSystemInfoRequest_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold RRC_PosSystemInfoRequest_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRC_PosSystemInfoRequest_r16_IEs__Format : T_Format RRC_PosSystemInfoRequest_r16_IEs__Type RRC_PosSystemInfoRequest_r16_IEs__cond :=
        proj2_format  RRC_PosSystemInfoRequest_r16_IEs__cond RRC_PosSystemInfoRequest_r16_IEs__list__Format
    RRC_PosSystemInfoRequest_r16_IEs__F1 RRC_PosSystemInfoRequest_r16_IEs__F2 RRC_PosSystemInfoRequest_r16_IEs__F1F2_cond  RRC_PosSystemInfoRequest_r16_IEs__F1F2_cond2 RRC_PosSystemInfoRequest_r16_IEs__F2F1_cond.
Opaque RRC_PosSystemInfoRequest_r16_IEs__cond RRC_PosSystemInfoRequest_r16_IEs__Format.

