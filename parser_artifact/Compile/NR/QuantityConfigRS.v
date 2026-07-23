Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FilterConfig.

Opaque FilterConfig__cond FilterConfig__Format.

Require Import NR.FilterConfig.

Opaque FilterConfig__cond FilterConfig__Format.

Record QuantityConfigRS__Type : Set :=
  make__QuantityConfigRS__Type {
    QuantityConfigRS__ssb_FilterConfig : FilterConfig__Type ;
    QuantityConfigRS__csi_RS_FilterConfig : FilterConfig__Type ;
}.
Definition QuantityConfigRS__list := (
 Nor FilterConfig__Type FilterConfig__cond ::
 Nor FilterConfig__Type FilterConfig__cond ::
 nil).
Definition QuantityConfigRS__cond z := 
  FilterConfig__cond (QuantityConfigRS__ssb_FilterConfig z) /\
  FilterConfig__cond (QuantityConfigRS__csi_RS_FilterConfig z) /\
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

Definition QuantityConfigRS__Format_Type := Eval cbn in seq_format_prod QuantityConfigRS__list.
Definition QuantityConfigRS__Format_list : QuantityConfigRS__Format_Type :=
  (FilterConfig__Format, (FilterConfig__Format, unit_format)).
Definition QuantityConfigRS__list__Format := (*Eval compute in *) seq_format QuantityConfigRS__list QuantityConfigRS__Format_list.
Definition QuantityConfigRS__F1 z :=
  (QuantityConfigRS__ssb_FilterConfig z, (QuantityConfigRS__csi_RS_FilterConfig z, tt)).
Definition QuantityConfigRS__F2 (y : seq_type QuantityConfigRS__list) :=
  match y with
  | (i0, (i1, _))=>
    make__QuantityConfigRS__Type i0 i1
  end.
Lemma QuantityConfigRS__F1F2_cond (z : QuantityConfigRS__Type)
  : QuantityConfigRS__cond z ->
  (seq_cond QuantityConfigRS__list (QuantityConfigRS__F1 z)).
intro H. unfold QuantityConfigRS__cond in H. simpl. auto. Qed.
Lemma QuantityConfigRS__F1F2_cond2 (z : QuantityConfigRS__Type)
 : QuantityConfigRS__F2 (QuantityConfigRS__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma QuantityConfigRS__F2F1_cond (y : seq_type QuantityConfigRS__list)
  : seq_cond QuantityConfigRS__list y ->
 (QuantityConfigRS__cond (QuantityConfigRS__F2 y)) /\  QuantityConfigRS__F1 (QuantityConfigRS__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold QuantityConfigRS__cond. simpl in *. auto.
 - simpl. unfold QuantityConfigRS__F1. simpl. destruct_all_unit. auto.   Qed.
Definition QuantityConfigRS__Format : T_Format QuantityConfigRS__Type QuantityConfigRS__cond :=
        proj2_format  QuantityConfigRS__cond QuantityConfigRS__list__Format
    QuantityConfigRS__F1 QuantityConfigRS__F2 QuantityConfigRS__F1F2_cond  QuantityConfigRS__F1F2_cond2 QuantityConfigRS__F2F1_cond.
Opaque QuantityConfigRS__cond QuantityConfigRS__Format.

