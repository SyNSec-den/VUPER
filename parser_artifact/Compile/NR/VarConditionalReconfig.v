Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.CondReconfigToAddModList_r16.

Opaque CondReconfigToAddModList_r16__cond CondReconfigToAddModList_r16__Format.

Record VarConditionalReconfig__Type : Set :=
  make__VarConditionalReconfig__Type {
    VarConditionalReconfig__condReconfigList : option CondReconfigToAddModList_r16__Type ;
}.
Definition VarConditionalReconfig__list := (
 Opt CondReconfigToAddModList_r16__Type CondReconfigToAddModList_r16__cond ::
 nil).
Definition VarConditionalReconfig__cond z := 
  opt_cond CondReconfigToAddModList_r16__cond (VarConditionalReconfig__condReconfigList z) /\
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

Definition VarConditionalReconfig__Format_Type := Eval cbn in seq_format_prod VarConditionalReconfig__list.
Definition VarConditionalReconfig__Format_list : VarConditionalReconfig__Format_Type :=
  (CondReconfigToAddModList_r16__Format, unit_format).
Definition VarConditionalReconfig__list__Format := (*Eval compute in *) seq_format VarConditionalReconfig__list VarConditionalReconfig__Format_list.
Definition VarConditionalReconfig__F1 z :=
  (VarConditionalReconfig__condReconfigList z, tt).
Definition VarConditionalReconfig__F2 (y : seq_type VarConditionalReconfig__list) :=
  match y with
  | (i0, _)=>
    make__VarConditionalReconfig__Type i0
  end.
Lemma VarConditionalReconfig__F1F2_cond (z : VarConditionalReconfig__Type)
  : VarConditionalReconfig__cond z ->
  (seq_cond VarConditionalReconfig__list (VarConditionalReconfig__F1 z)).
intro H. unfold VarConditionalReconfig__cond in H. simpl. auto. Qed.
Lemma VarConditionalReconfig__F1F2_cond2 (z : VarConditionalReconfig__Type)
 : VarConditionalReconfig__F2 (VarConditionalReconfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarConditionalReconfig__F2F1_cond (y : seq_type VarConditionalReconfig__list)
  : seq_cond VarConditionalReconfig__list y ->
 (VarConditionalReconfig__cond (VarConditionalReconfig__F2 y)) /\  VarConditionalReconfig__F1 (VarConditionalReconfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarConditionalReconfig__cond. simpl in *. auto.
 - simpl. unfold VarConditionalReconfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarConditionalReconfig__Format : T_Format VarConditionalReconfig__Type VarConditionalReconfig__cond :=
        proj2_format  VarConditionalReconfig__cond VarConditionalReconfig__list__Format
    VarConditionalReconfig__F1 VarConditionalReconfig__F2 VarConditionalReconfig__F1F2_cond  VarConditionalReconfig__F1F2_cond2 VarConditionalReconfig__F2F1_cond.
Opaque VarConditionalReconfig__cond VarConditionalReconfig__Format.

