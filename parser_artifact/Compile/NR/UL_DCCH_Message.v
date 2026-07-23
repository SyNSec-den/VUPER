Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UL_DCCH_MessageType.

Opaque UL_DCCH_MessageType__cond UL_DCCH_MessageType__Format.

Record UL_DCCH_Message__Type : Set :=
  make__UL_DCCH_Message__Type {
    UL_DCCH_Message__message : UL_DCCH_MessageType__Type ;
}.
Definition UL_DCCH_Message__list := (
 Nor UL_DCCH_MessageType__Type UL_DCCH_MessageType__cond ::
 nil).
Definition UL_DCCH_Message__cond z := 
  UL_DCCH_MessageType__cond (UL_DCCH_Message__message z) /\
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

Definition UL_DCCH_Message__Format_Type := Eval cbn in seq_format_prod UL_DCCH_Message__list.
Definition UL_DCCH_Message__Format_list : UL_DCCH_Message__Format_Type :=
  (UL_DCCH_MessageType__Format, unit_format).
Definition UL_DCCH_Message__list__Format := (*Eval compute in *) seq_format UL_DCCH_Message__list UL_DCCH_Message__Format_list.
Definition UL_DCCH_Message__F1 z :=
  (UL_DCCH_Message__message z, tt).
Definition UL_DCCH_Message__F2 (y : seq_type UL_DCCH_Message__list) :=
  match y with
  | (i0, _)=>
    make__UL_DCCH_Message__Type i0
  end.
Lemma UL_DCCH_Message__F1F2_cond (z : UL_DCCH_Message__Type)
  : UL_DCCH_Message__cond z ->
  (seq_cond UL_DCCH_Message__list (UL_DCCH_Message__F1 z)).
intro H. unfold UL_DCCH_Message__cond in H. simpl. auto. Qed.
Lemma UL_DCCH_Message__F1F2_cond2 (z : UL_DCCH_Message__Type)
 : UL_DCCH_Message__F2 (UL_DCCH_Message__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UL_DCCH_Message__F2F1_cond (y : seq_type UL_DCCH_Message__list)
  : seq_cond UL_DCCH_Message__list y ->
 (UL_DCCH_Message__cond (UL_DCCH_Message__F2 y)) /\  UL_DCCH_Message__F1 (UL_DCCH_Message__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UL_DCCH_Message__cond. simpl in *. auto.
 - simpl. unfold UL_DCCH_Message__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UL_DCCH_Message__Format : T_Format UL_DCCH_Message__Type UL_DCCH_Message__cond :=
        proj2_format  UL_DCCH_Message__cond UL_DCCH_Message__list__Format
    UL_DCCH_Message__F1 UL_DCCH_Message__F2 UL_DCCH_Message__F1F2_cond  UL_DCCH_Message__F1F2_cond2 UL_DCCH_Message__F2F1_cond.
Opaque UL_DCCH_Message__cond UL_DCCH_Message__Format.

