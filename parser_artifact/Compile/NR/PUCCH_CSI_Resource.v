Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Record PUCCH_CSI_Resource__Type : Set :=
  make__PUCCH_CSI_Resource__Type {
    PUCCH_CSI_Resource__uplinkBandwidthPartId : BWP_Id__Type ;
    PUCCH_CSI_Resource__pucch_Resource : PUCCH_ResourceId__Type ;
}.
Definition PUCCH_CSI_Resource__list := (
 Nor BWP_Id__Type BWP_Id__cond ::
 Nor PUCCH_ResourceId__Type PUCCH_ResourceId__cond ::
 nil).
Definition PUCCH_CSI_Resource__cond z := 
  BWP_Id__cond (PUCCH_CSI_Resource__uplinkBandwidthPartId z) /\
  PUCCH_ResourceId__cond (PUCCH_CSI_Resource__pucch_Resource z) /\
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

Definition PUCCH_CSI_Resource__Format_Type := Eval cbn in seq_format_prod PUCCH_CSI_Resource__list.
Definition PUCCH_CSI_Resource__Format_list : PUCCH_CSI_Resource__Format_Type :=
  (BWP_Id__Format, (PUCCH_ResourceId__Format, unit_format)).
Definition PUCCH_CSI_Resource__list__Format := (*Eval compute in *) seq_format PUCCH_CSI_Resource__list PUCCH_CSI_Resource__Format_list.
Definition PUCCH_CSI_Resource__F1 z :=
  (PUCCH_CSI_Resource__uplinkBandwidthPartId z, (PUCCH_CSI_Resource__pucch_Resource z, tt)).
Definition PUCCH_CSI_Resource__F2 (y : seq_type PUCCH_CSI_Resource__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUCCH_CSI_Resource__Type i0 i1
  end.
Lemma PUCCH_CSI_Resource__F1F2_cond (z : PUCCH_CSI_Resource__Type)
  : PUCCH_CSI_Resource__cond z ->
  (seq_cond PUCCH_CSI_Resource__list (PUCCH_CSI_Resource__F1 z)).
intro H. unfold PUCCH_CSI_Resource__cond in H. simpl. auto. Qed.
Lemma PUCCH_CSI_Resource__F1F2_cond2 (z : PUCCH_CSI_Resource__Type)
 : PUCCH_CSI_Resource__F2 (PUCCH_CSI_Resource__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_CSI_Resource__F2F1_cond (y : seq_type PUCCH_CSI_Resource__list)
  : seq_cond PUCCH_CSI_Resource__list y ->
 (PUCCH_CSI_Resource__cond (PUCCH_CSI_Resource__F2 y)) /\  PUCCH_CSI_Resource__F1 (PUCCH_CSI_Resource__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_CSI_Resource__cond. simpl in *. auto.
 - simpl. unfold PUCCH_CSI_Resource__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_CSI_Resource__Format : T_Format PUCCH_CSI_Resource__Type PUCCH_CSI_Resource__cond :=
        proj2_format  PUCCH_CSI_Resource__cond PUCCH_CSI_Resource__list__Format
    PUCCH_CSI_Resource__F1 PUCCH_CSI_Resource__F2 PUCCH_CSI_Resource__F1F2_cond  PUCCH_CSI_Resource__F1F2_cond2 PUCCH_CSI_Resource__F2F1_cond.
Opaque PUCCH_CSI_Resource__cond PUCCH_CSI_Resource__Format.

