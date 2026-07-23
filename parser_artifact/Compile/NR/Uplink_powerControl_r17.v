Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.Uplink_powerControlId_r17.

Opaque Uplink_powerControlId_r17__cond Uplink_powerControlId_r17__Format.

Require Import NR.P0AlphaSet_r17.

Opaque P0AlphaSet_r17__cond P0AlphaSet_r17__Format.

Require Import NR.P0AlphaSet_r17.

Opaque P0AlphaSet_r17__cond P0AlphaSet_r17__Format.

Require Import NR.P0AlphaSet_r17.

Opaque P0AlphaSet_r17__cond P0AlphaSet_r17__Format.

Record Uplink_powerControl_r17__Type : Set :=
  make__Uplink_powerControl_r17__Type {
    Uplink_powerControl_r17__ul_powercontrolId_r17 : Uplink_powerControlId_r17__Type ;
    Uplink_powerControl_r17__p0AlphaSetforPUSCH_r17 : option P0AlphaSet_r17__Type ;
    Uplink_powerControl_r17__p0AlphaSetforPUCCH_r17 : option P0AlphaSet_r17__Type ;
    Uplink_powerControl_r17__p0AlphaSetforSRS_r17 : option P0AlphaSet_r17__Type ;
}.
Definition Uplink_powerControl_r17__list := (
 Nor Uplink_powerControlId_r17__Type Uplink_powerControlId_r17__cond ::
 Opt P0AlphaSet_r17__Type P0AlphaSet_r17__cond ::
 Opt P0AlphaSet_r17__Type P0AlphaSet_r17__cond ::
 Opt P0AlphaSet_r17__Type P0AlphaSet_r17__cond ::
 nil).
Definition Uplink_powerControl_r17__cond z := 
  Uplink_powerControlId_r17__cond (Uplink_powerControl_r17__ul_powercontrolId_r17 z) /\
  opt_cond P0AlphaSet_r17__cond (Uplink_powerControl_r17__p0AlphaSetforPUSCH_r17 z) /\
  opt_cond P0AlphaSet_r17__cond (Uplink_powerControl_r17__p0AlphaSetforPUCCH_r17 z) /\
  opt_cond P0AlphaSet_r17__cond (Uplink_powerControl_r17__p0AlphaSetforSRS_r17 z) /\
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

Definition Uplink_powerControl_r17__Format_Type := Eval cbn in seq_format_prod Uplink_powerControl_r17__list.
Definition Uplink_powerControl_r17__Format_list : Uplink_powerControl_r17__Format_Type :=
  (Uplink_powerControlId_r17__Format, (P0AlphaSet_r17__Format, (P0AlphaSet_r17__Format, (P0AlphaSet_r17__Format, unit_format)))).
Definition Uplink_powerControl_r17__list__Format := (*Eval compute in *) seq_format Uplink_powerControl_r17__list Uplink_powerControl_r17__Format_list.
Definition Uplink_powerControl_r17__F1 z :=
  (Uplink_powerControl_r17__ul_powercontrolId_r17 z, (Uplink_powerControl_r17__p0AlphaSetforPUSCH_r17 z, (Uplink_powerControl_r17__p0AlphaSetforPUCCH_r17 z, (Uplink_powerControl_r17__p0AlphaSetforSRS_r17 z, tt)))).
Definition Uplink_powerControl_r17__F2 (y : seq_type Uplink_powerControl_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__Uplink_powerControl_r17__Type i0 i1 i2 i3
  end.
Lemma Uplink_powerControl_r17__F1F2_cond (z : Uplink_powerControl_r17__Type)
  : Uplink_powerControl_r17__cond z ->
  (seq_cond Uplink_powerControl_r17__list (Uplink_powerControl_r17__F1 z)).
intro H. unfold Uplink_powerControl_r17__cond in H. simpl. auto. Qed.
Lemma Uplink_powerControl_r17__F1F2_cond2 (z : Uplink_powerControl_r17__Type)
 : Uplink_powerControl_r17__F2 (Uplink_powerControl_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Uplink_powerControl_r17__F2F1_cond (y : seq_type Uplink_powerControl_r17__list)
  : seq_cond Uplink_powerControl_r17__list y ->
 (Uplink_powerControl_r17__cond (Uplink_powerControl_r17__F2 y)) /\  Uplink_powerControl_r17__F1 (Uplink_powerControl_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Uplink_powerControl_r17__cond. simpl in *. auto.
 - simpl. unfold Uplink_powerControl_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Uplink_powerControl_r17__Format : T_Format Uplink_powerControl_r17__Type Uplink_powerControl_r17__cond :=
        proj2_format  Uplink_powerControl_r17__cond Uplink_powerControl_r17__list__Format
    Uplink_powerControl_r17__F1 Uplink_powerControl_r17__F2 Uplink_powerControl_r17__F1F2_cond  Uplink_powerControl_r17__F1F2_cond2 Uplink_powerControl_r17__F2F1_cond.
Opaque Uplink_powerControl_r17__cond Uplink_powerControl_r17__Format.

