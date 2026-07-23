Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SlotBased_v1630.
Definition RepetitionSchemeConfig_v1630__slotBased_v1630__Type := SetupRelease__Type SlotBased_v1630__Type.
Definition RepetitionSchemeConfig_v1630__slotBased_v1630__cond := SetupRelease__cond _ SlotBased_v1630__cond.
Definition RepetitionSchemeConfig_v1630__slotBased_v1630__Format : T_Format RepetitionSchemeConfig_v1630__slotBased_v1630__Type RepetitionSchemeConfig_v1630__slotBased_v1630__cond := SetupRelease__Format _ _ SlotBased_v1630__Format.
Opaque RepetitionSchemeConfig_v1630__slotBased_v1630__cond RepetitionSchemeConfig_v1630__slotBased_v1630__Format.

Record RepetitionSchemeConfig_v1630__Type : Set :=
  make__RepetitionSchemeConfig_v1630__Type {
    RepetitionSchemeConfig_v1630__slotBased_v1630 : RepetitionSchemeConfig_v1630__slotBased_v1630__Type ;
}.
Definition RepetitionSchemeConfig_v1630__list := (
 Nor RepetitionSchemeConfig_v1630__slotBased_v1630__Type RepetitionSchemeConfig_v1630__slotBased_v1630__cond ::
 nil).
Definition RepetitionSchemeConfig_v1630__cond z := 
  RepetitionSchemeConfig_v1630__slotBased_v1630__cond (RepetitionSchemeConfig_v1630__slotBased_v1630 z) /\
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
Opaque RepetitionSchemeConfig_v1630__slotBased_v1630__cond RepetitionSchemeConfig_v1630__slotBased_v1630__Format.


Definition RepetitionSchemeConfig_v1630__Format_Type := Eval cbn in seq_format_prod RepetitionSchemeConfig_v1630__list.
Definition RepetitionSchemeConfig_v1630__Format_list : RepetitionSchemeConfig_v1630__Format_Type :=
  (RepetitionSchemeConfig_v1630__slotBased_v1630__Format, unit_format).
Definition RepetitionSchemeConfig_v1630__list__Format := (*Eval compute in *) seq_format RepetitionSchemeConfig_v1630__list RepetitionSchemeConfig_v1630__Format_list.
Definition RepetitionSchemeConfig_v1630__F1 z :=
  (RepetitionSchemeConfig_v1630__slotBased_v1630 z, tt).
Definition RepetitionSchemeConfig_v1630__F2 (y : seq_type RepetitionSchemeConfig_v1630__list) :=
  match y with
  | (i0, _)=>
    make__RepetitionSchemeConfig_v1630__Type i0
  end.
Lemma RepetitionSchemeConfig_v1630__F1F2_cond (z : RepetitionSchemeConfig_v1630__Type)
  : RepetitionSchemeConfig_v1630__cond z ->
  (seq_cond RepetitionSchemeConfig_v1630__list (RepetitionSchemeConfig_v1630__F1 z)).
intro H. unfold RepetitionSchemeConfig_v1630__cond in H. simpl. auto. Qed.
Lemma RepetitionSchemeConfig_v1630__F1F2_cond2 (z : RepetitionSchemeConfig_v1630__Type)
 : RepetitionSchemeConfig_v1630__F2 (RepetitionSchemeConfig_v1630__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RepetitionSchemeConfig_v1630__F2F1_cond (y : seq_type RepetitionSchemeConfig_v1630__list)
  : seq_cond RepetitionSchemeConfig_v1630__list y ->
 (RepetitionSchemeConfig_v1630__cond (RepetitionSchemeConfig_v1630__F2 y)) /\  RepetitionSchemeConfig_v1630__F1 (RepetitionSchemeConfig_v1630__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RepetitionSchemeConfig_v1630__cond. simpl in *. auto.
 - simpl. unfold RepetitionSchemeConfig_v1630__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RepetitionSchemeConfig_v1630__Format : T_Format RepetitionSchemeConfig_v1630__Type RepetitionSchemeConfig_v1630__cond :=
        proj2_format  RepetitionSchemeConfig_v1630__cond RepetitionSchemeConfig_v1630__list__Format
    RepetitionSchemeConfig_v1630__F1 RepetitionSchemeConfig_v1630__F2 RepetitionSchemeConfig_v1630__F1F2_cond  RepetitionSchemeConfig_v1630__F1F2_cond2 RepetitionSchemeConfig_v1630__F2F1_cond.
Opaque RepetitionSchemeConfig_v1630__cond RepetitionSchemeConfig_v1630__Format.

