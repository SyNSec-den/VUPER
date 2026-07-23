Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DL_DCCH_MessageType.

Opaque DL_DCCH_MessageType__cond DL_DCCH_MessageType__Format.

Record DL_DCCH_Message__Type : Set :=
  make__DL_DCCH_Message__Type {
    DL_DCCH_Message__message : DL_DCCH_MessageType__Type ;
}.
Definition DL_DCCH_Message__list := (
 Nor DL_DCCH_MessageType__Type DL_DCCH_MessageType__cond ::
 nil).
Definition DL_DCCH_Message__cond z := 
  DL_DCCH_MessageType__cond (DL_DCCH_Message__message z) /\
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

Definition DL_DCCH_Message__Format_Type := Eval cbn in seq_format_prod DL_DCCH_Message__list.
Definition DL_DCCH_Message__Format_list : DL_DCCH_Message__Format_Type :=
  (DL_DCCH_MessageType__Format, unit_format).
Definition DL_DCCH_Message__list__Format := (*Eval compute in *) seq_format DL_DCCH_Message__list DL_DCCH_Message__Format_list.
Definition DL_DCCH_Message__F1 z :=
  (DL_DCCH_Message__message z, tt).
Definition DL_DCCH_Message__F2 (y : seq_type DL_DCCH_Message__list) :=
  match y with
  | (i0, _)=>
    make__DL_DCCH_Message__Type i0
  end.
Lemma DL_DCCH_Message__F1F2_cond (z : DL_DCCH_Message__Type)
  : DL_DCCH_Message__cond z ->
  (seq_cond DL_DCCH_Message__list (DL_DCCH_Message__F1 z)).
intro H. unfold DL_DCCH_Message__cond in H. simpl. auto. Qed.
Lemma DL_DCCH_Message__F1F2_cond2 (z : DL_DCCH_Message__Type)
 : DL_DCCH_Message__F2 (DL_DCCH_Message__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DL_DCCH_Message__F2F1_cond (y : seq_type DL_DCCH_Message__list)
  : seq_cond DL_DCCH_Message__list y ->
 (DL_DCCH_Message__cond (DL_DCCH_Message__F2 y)) /\  DL_DCCH_Message__F1 (DL_DCCH_Message__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DL_DCCH_Message__cond. simpl in *. auto.
 - simpl. unfold DL_DCCH_Message__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DL_DCCH_Message__Format : T_Format DL_DCCH_Message__Type DL_DCCH_Message__cond :=
        proj2_format  DL_DCCH_Message__cond DL_DCCH_Message__list__Format
    DL_DCCH_Message__F1 DL_DCCH_Message__F2 DL_DCCH_Message__F1F2_cond  DL_DCCH_Message__F1F2_cond2 DL_DCCH_Message__F2F1_cond.
Opaque DL_DCCH_Message__cond DL_DCCH_Message__Format.

