Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.SCCH_MessageType.

Opaque SCCH_MessageType__cond SCCH_MessageType__Format.

Record SCCH_Message__Type : Set :=
  make__SCCH_Message__Type {
    SCCH_Message__message : SCCH_MessageType__Type ;
}.
Definition SCCH_Message__list := (
 Nor SCCH_MessageType__Type SCCH_MessageType__cond ::
 nil).
Definition SCCH_Message__cond z := 
  SCCH_MessageType__cond (SCCH_Message__message z) /\
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

Definition SCCH_Message__Format_Type := Eval cbn in seq_format_prod SCCH_Message__list.
Definition SCCH_Message__Format_list : SCCH_Message__Format_Type :=
  (SCCH_MessageType__Format, unit_format).
Definition SCCH_Message__list__Format := (*Eval compute in *) seq_format SCCH_Message__list SCCH_Message__Format_list.
Definition SCCH_Message__F1 z :=
  (SCCH_Message__message z, tt).
Definition SCCH_Message__F2 (y : seq_type SCCH_Message__list) :=
  match y with
  | (i0, _)=>
    make__SCCH_Message__Type i0
  end.
Lemma SCCH_Message__F1F2_cond (z : SCCH_Message__Type)
  : SCCH_Message__cond z ->
  (seq_cond SCCH_Message__list (SCCH_Message__F1 z)).
intro H. unfold SCCH_Message__cond in H. simpl. auto. Qed.
Lemma SCCH_Message__F1F2_cond2 (z : SCCH_Message__Type)
 : SCCH_Message__F2 (SCCH_Message__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SCCH_Message__F2F1_cond (y : seq_type SCCH_Message__list)
  : seq_cond SCCH_Message__list y ->
 (SCCH_Message__cond (SCCH_Message__F2 y)) /\  SCCH_Message__F1 (SCCH_Message__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SCCH_Message__cond. simpl in *. auto.
 - simpl. unfold SCCH_Message__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SCCH_Message__Format : T_Format SCCH_Message__Type SCCH_Message__cond :=
        proj2_format  SCCH_Message__cond SCCH_Message__list__Format
    SCCH_Message__F1 SCCH_Message__F2 SCCH_Message__F1F2_cond  SCCH_Message__F1F2_cond2 SCCH_Message__F2F1_cond.
Opaque SCCH_Message__cond SCCH_Message__Format.

