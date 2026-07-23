Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_ResourceId.

Opaque SRS_ResourceId__cond SRS_ResourceId__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Record PUCCH_SRS__Type : Set :=
  make__PUCCH_SRS__Type {
    PUCCH_SRS__resource : SRS_ResourceId__Type ;
    PUCCH_SRS__uplinkBWP : BWP_Id__Type ;
}.
Definition PUCCH_SRS__list := (
 Nor SRS_ResourceId__Type SRS_ResourceId__cond ::
 Nor BWP_Id__Type BWP_Id__cond ::
 nil).
Definition PUCCH_SRS__cond z := 
  SRS_ResourceId__cond (PUCCH_SRS__resource z) /\
  BWP_Id__cond (PUCCH_SRS__uplinkBWP z) /\
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

Definition PUCCH_SRS__Format_Type := Eval cbn in seq_format_prod PUCCH_SRS__list.
Definition PUCCH_SRS__Format_list : PUCCH_SRS__Format_Type :=
  (SRS_ResourceId__Format, (BWP_Id__Format, unit_format)).
Definition PUCCH_SRS__list__Format := (*Eval compute in *) seq_format PUCCH_SRS__list PUCCH_SRS__Format_list.
Definition PUCCH_SRS__F1 z :=
  (PUCCH_SRS__resource z, (PUCCH_SRS__uplinkBWP z, tt)).
Definition PUCCH_SRS__F2 (y : seq_type PUCCH_SRS__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUCCH_SRS__Type i0 i1
  end.
Lemma PUCCH_SRS__F1F2_cond (z : PUCCH_SRS__Type)
  : PUCCH_SRS__cond z ->
  (seq_cond PUCCH_SRS__list (PUCCH_SRS__F1 z)).
intro H. unfold PUCCH_SRS__cond in H. simpl. auto. Qed.
Lemma PUCCH_SRS__F1F2_cond2 (z : PUCCH_SRS__Type)
 : PUCCH_SRS__F2 (PUCCH_SRS__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_SRS__F2F1_cond (y : seq_type PUCCH_SRS__list)
  : seq_cond PUCCH_SRS__list y ->
 (PUCCH_SRS__cond (PUCCH_SRS__F2 y)) /\  PUCCH_SRS__F1 (PUCCH_SRS__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_SRS__cond. simpl in *. auto.
 - simpl. unfold PUCCH_SRS__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_SRS__Format : T_Format PUCCH_SRS__Type PUCCH_SRS__cond :=
        proj2_format  PUCCH_SRS__cond PUCCH_SRS__list__Format
    PUCCH_SRS__F1 PUCCH_SRS__F2 PUCCH_SRS__F1F2_cond  PUCCH_SRS__F1F2_cond2 PUCCH_SRS__F2F1_cond.
Opaque PUCCH_SRS__cond PUCCH_SRS__Format.

