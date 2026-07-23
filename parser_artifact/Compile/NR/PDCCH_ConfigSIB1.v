Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ControlResourceSetZero.

Opaque ControlResourceSetZero__cond ControlResourceSetZero__Format.

Require Import NR.SearchSpaceZero.

Opaque SearchSpaceZero__cond SearchSpaceZero__Format.

Record PDCCH_ConfigSIB1__Type : Set :=
  make__PDCCH_ConfigSIB1__Type {
    PDCCH_ConfigSIB1__controlResourceSetZero : ControlResourceSetZero__Type ;
    PDCCH_ConfigSIB1__searchSpaceZero : SearchSpaceZero__Type ;
}.
Definition PDCCH_ConfigSIB1__list := (
 Nor ControlResourceSetZero__Type ControlResourceSetZero__cond ::
 Nor SearchSpaceZero__Type SearchSpaceZero__cond ::
 nil).
Definition PDCCH_ConfigSIB1__cond z := 
  ControlResourceSetZero__cond (PDCCH_ConfigSIB1__controlResourceSetZero z) /\
  SearchSpaceZero__cond (PDCCH_ConfigSIB1__searchSpaceZero z) /\
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

Definition PDCCH_ConfigSIB1__Format_Type := Eval cbn in seq_format_prod PDCCH_ConfigSIB1__list.
Definition PDCCH_ConfigSIB1__Format_list : PDCCH_ConfigSIB1__Format_Type :=
  (ControlResourceSetZero__Format, (SearchSpaceZero__Format, unit_format)).
Definition PDCCH_ConfigSIB1__list__Format := (*Eval compute in *) seq_format PDCCH_ConfigSIB1__list PDCCH_ConfigSIB1__Format_list.
Definition PDCCH_ConfigSIB1__F1 z :=
  (PDCCH_ConfigSIB1__controlResourceSetZero z, (PDCCH_ConfigSIB1__searchSpaceZero z, tt)).
Definition PDCCH_ConfigSIB1__F2 (y : seq_type PDCCH_ConfigSIB1__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDCCH_ConfigSIB1__Type i0 i1
  end.
Lemma PDCCH_ConfigSIB1__F1F2_cond (z : PDCCH_ConfigSIB1__Type)
  : PDCCH_ConfigSIB1__cond z ->
  (seq_cond PDCCH_ConfigSIB1__list (PDCCH_ConfigSIB1__F1 z)).
intro H. unfold PDCCH_ConfigSIB1__cond in H. simpl. auto. Qed.
Lemma PDCCH_ConfigSIB1__F1F2_cond2 (z : PDCCH_ConfigSIB1__Type)
 : PDCCH_ConfigSIB1__F2 (PDCCH_ConfigSIB1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_ConfigSIB1__F2F1_cond (y : seq_type PDCCH_ConfigSIB1__list)
  : seq_cond PDCCH_ConfigSIB1__list y ->
 (PDCCH_ConfigSIB1__cond (PDCCH_ConfigSIB1__F2 y)) /\  PDCCH_ConfigSIB1__F1 (PDCCH_ConfigSIB1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_ConfigSIB1__cond. simpl in *. auto.
 - simpl. unfold PDCCH_ConfigSIB1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_ConfigSIB1__Format : T_Format PDCCH_ConfigSIB1__Type PDCCH_ConfigSIB1__cond :=
        proj2_format  PDCCH_ConfigSIB1__cond PDCCH_ConfigSIB1__list__Format
    PDCCH_ConfigSIB1__F1 PDCCH_ConfigSIB1__F2 PDCCH_ConfigSIB1__F1F2_cond  PDCCH_ConfigSIB1__F1F2_cond2 PDCCH_ConfigSIB1__F2F1_cond.
Opaque PDCCH_ConfigSIB1__cond PDCCH_ConfigSIB1__Format.

