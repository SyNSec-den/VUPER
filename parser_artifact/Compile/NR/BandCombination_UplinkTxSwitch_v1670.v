Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandCombination_v15g0.

Opaque BandCombination_v15g0__cond BandCombination_v15g0__Format.

Record BandCombination_UplinkTxSwitch_v1670__Type : Set :=
  make__BandCombination_UplinkTxSwitch_v1670__Type {
    BandCombination_UplinkTxSwitch_v1670__bandCombination_v15g0 : option BandCombination_v15g0__Type ;
}.
Definition BandCombination_UplinkTxSwitch_v1670__list := (
 Opt BandCombination_v15g0__Type BandCombination_v15g0__cond ::
 nil).
Definition BandCombination_UplinkTxSwitch_v1670__cond z := 
  opt_cond BandCombination_v15g0__cond (BandCombination_UplinkTxSwitch_v1670__bandCombination_v15g0 z) /\
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

Definition BandCombination_UplinkTxSwitch_v1670__Format_Type := Eval cbn in seq_format_prod BandCombination_UplinkTxSwitch_v1670__list.
Definition BandCombination_UplinkTxSwitch_v1670__Format_list : BandCombination_UplinkTxSwitch_v1670__Format_Type :=
  (BandCombination_v15g0__Format, unit_format).
Definition BandCombination_UplinkTxSwitch_v1670__list__Format := (*Eval compute in *) seq_format BandCombination_UplinkTxSwitch_v1670__list BandCombination_UplinkTxSwitch_v1670__Format_list.
Definition BandCombination_UplinkTxSwitch_v1670__F1 z :=
  (BandCombination_UplinkTxSwitch_v1670__bandCombination_v15g0 z, tt).
Definition BandCombination_UplinkTxSwitch_v1670__F2 (y : seq_type BandCombination_UplinkTxSwitch_v1670__list) :=
  match y with
  | (i0, _)=>
    make__BandCombination_UplinkTxSwitch_v1670__Type i0
  end.
Lemma BandCombination_UplinkTxSwitch_v1670__F1F2_cond (z : BandCombination_UplinkTxSwitch_v1670__Type)
  : BandCombination_UplinkTxSwitch_v1670__cond z ->
  (seq_cond BandCombination_UplinkTxSwitch_v1670__list (BandCombination_UplinkTxSwitch_v1670__F1 z)).
intro H. unfold BandCombination_UplinkTxSwitch_v1670__cond in H. simpl. auto. Qed.
Lemma BandCombination_UplinkTxSwitch_v1670__F1F2_cond2 (z : BandCombination_UplinkTxSwitch_v1670__Type)
 : BandCombination_UplinkTxSwitch_v1670__F2 (BandCombination_UplinkTxSwitch_v1670__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombination_UplinkTxSwitch_v1670__F2F1_cond (y : seq_type BandCombination_UplinkTxSwitch_v1670__list)
  : seq_cond BandCombination_UplinkTxSwitch_v1670__list y ->
 (BandCombination_UplinkTxSwitch_v1670__cond (BandCombination_UplinkTxSwitch_v1670__F2 y)) /\  BandCombination_UplinkTxSwitch_v1670__F1 (BandCombination_UplinkTxSwitch_v1670__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombination_UplinkTxSwitch_v1670__cond. simpl in *. auto.
 - simpl. unfold BandCombination_UplinkTxSwitch_v1670__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombination_UplinkTxSwitch_v1670__Format : T_Format BandCombination_UplinkTxSwitch_v1670__Type BandCombination_UplinkTxSwitch_v1670__cond :=
        proj2_format  BandCombination_UplinkTxSwitch_v1670__cond BandCombination_UplinkTxSwitch_v1670__list__Format
    BandCombination_UplinkTxSwitch_v1670__F1 BandCombination_UplinkTxSwitch_v1670__F2 BandCombination_UplinkTxSwitch_v1670__F1F2_cond  BandCombination_UplinkTxSwitch_v1670__F1F2_cond2 BandCombination_UplinkTxSwitch_v1670__F2F1_cond.
Opaque BandCombination_UplinkTxSwitch_v1670__cond BandCombination_UplinkTxSwitch_v1670__Format.

