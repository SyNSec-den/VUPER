Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PCCH_MessageType.

Opaque PCCH_MessageType__cond PCCH_MessageType__Format.

Record PCCH_Message__Type : Set :=
  make__PCCH_Message__Type {
    PCCH_Message__message : PCCH_MessageType__Type ;
}.
Definition PCCH_Message__list := (
 Nor PCCH_MessageType__Type PCCH_MessageType__cond ::
 nil).
Definition PCCH_Message__cond z := 
  PCCH_MessageType__cond (PCCH_Message__message z) /\
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

Definition PCCH_Message__Format_Type := Eval cbn in seq_format_prod PCCH_Message__list.
Definition PCCH_Message__Format_list : PCCH_Message__Format_Type :=
  (PCCH_MessageType__Format, unit_format).
Definition PCCH_Message__list__Format := (*Eval compute in *) seq_format PCCH_Message__list PCCH_Message__Format_list.
Definition PCCH_Message__F1 z :=
  (PCCH_Message__message z, tt).
Definition PCCH_Message__F2 (y : seq_type PCCH_Message__list) :=
  match y with
  | (i0, _)=>
    make__PCCH_Message__Type i0
  end.
Lemma PCCH_Message__F1F2_cond (z : PCCH_Message__Type)
  : PCCH_Message__cond z ->
  (seq_cond PCCH_Message__list (PCCH_Message__F1 z)).
intro H. unfold PCCH_Message__cond in H. simpl. auto. Qed.
Lemma PCCH_Message__F1F2_cond2 (z : PCCH_Message__Type)
 : PCCH_Message__F2 (PCCH_Message__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PCCH_Message__F2F1_cond (y : seq_type PCCH_Message__list)
  : seq_cond PCCH_Message__list y ->
 (PCCH_Message__cond (PCCH_Message__F2 y)) /\  PCCH_Message__F1 (PCCH_Message__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PCCH_Message__cond. simpl in *. auto.
 - simpl. unfold PCCH_Message__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PCCH_Message__Format : T_Format PCCH_Message__Type PCCH_Message__cond :=
        proj2_format  PCCH_Message__cond PCCH_Message__list__Format
    PCCH_Message__F1 PCCH_Message__F2 PCCH_Message__F1F2_cond  PCCH_Message__F1F2_cond2 PCCH_Message__F2F1_cond.
Opaque PCCH_Message__cond PCCH_Message__Format.

