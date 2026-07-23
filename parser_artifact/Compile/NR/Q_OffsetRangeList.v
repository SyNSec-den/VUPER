Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma Q_OffsetRangeList__rsrpOffsetSSB__dft_helper : Q_OffsetRange__cond Q_OffsetRange__dB0. apply I. Qed.
Definition Q_OffsetRangeList__rsrpOffsetSSB__dft_helper2 : forall (x y : Q_OffsetRange__Type), {x = y} + {x <> y}. decide equality. Defined.
Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma Q_OffsetRangeList__rsrqOffsetSSB__dft_helper : Q_OffsetRange__cond Q_OffsetRange__dB0. apply I. Qed.
Definition Q_OffsetRangeList__rsrqOffsetSSB__dft_helper2 : forall (x y : Q_OffsetRange__Type), {x = y} + {x <> y}. decide equality. Defined.
Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma Q_OffsetRangeList__sinrOffsetSSB__dft_helper : Q_OffsetRange__cond Q_OffsetRange__dB0. apply I. Qed.
Definition Q_OffsetRangeList__sinrOffsetSSB__dft_helper2 : forall (x y : Q_OffsetRange__Type), {x = y} + {x <> y}. decide equality. Defined.
Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma Q_OffsetRangeList__rsrpOffsetCSI_RS__dft_helper : Q_OffsetRange__cond Q_OffsetRange__dB0. apply I. Qed.
Definition Q_OffsetRangeList__rsrpOffsetCSI_RS__dft_helper2 : forall (x y : Q_OffsetRange__Type), {x = y} + {x <> y}. decide equality. Defined.
Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma Q_OffsetRangeList__rsrqOffsetCSI_RS__dft_helper : Q_OffsetRange__cond Q_OffsetRange__dB0. apply I. Qed.
Definition Q_OffsetRangeList__rsrqOffsetCSI_RS__dft_helper2 : forall (x y : Q_OffsetRange__Type), {x = y} + {x <> y}. decide equality. Defined.
Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma Q_OffsetRangeList__sinrOffsetCSI_RS__dft_helper : Q_OffsetRange__cond Q_OffsetRange__dB0. apply I. Qed.
Definition Q_OffsetRangeList__sinrOffsetCSI_RS__dft_helper2 : forall (x y : Q_OffsetRange__Type), {x = y} + {x <> y}. decide equality. Defined.
Record Q_OffsetRangeList__Type : Set :=
  make__Q_OffsetRangeList__Type {
    Q_OffsetRangeList__rsrpOffsetSSB : Q_OffsetRange__Type ;
    Q_OffsetRangeList__rsrqOffsetSSB : Q_OffsetRange__Type ;
    Q_OffsetRangeList__sinrOffsetSSB : Q_OffsetRange__Type ;
    Q_OffsetRangeList__rsrpOffsetCSI_RS : Q_OffsetRange__Type ;
    Q_OffsetRangeList__rsrqOffsetCSI_RS : Q_OffsetRange__Type ;
    Q_OffsetRangeList__sinrOffsetCSI_RS : Q_OffsetRange__Type ;
}.
Definition Q_OffsetRangeList__list := (
 Dft Q_OffsetRange__Type Q_OffsetRange__cond Q_OffsetRange__dB0 Q_OffsetRangeList__rsrpOffsetSSB__dft_helper Q_OffsetRangeList__rsrpOffsetSSB__dft_helper2 ::
 Dft Q_OffsetRange__Type Q_OffsetRange__cond Q_OffsetRange__dB0 Q_OffsetRangeList__rsrqOffsetSSB__dft_helper Q_OffsetRangeList__rsrqOffsetSSB__dft_helper2 ::
 Dft Q_OffsetRange__Type Q_OffsetRange__cond Q_OffsetRange__dB0 Q_OffsetRangeList__sinrOffsetSSB__dft_helper Q_OffsetRangeList__sinrOffsetSSB__dft_helper2 ::
 Dft Q_OffsetRange__Type Q_OffsetRange__cond Q_OffsetRange__dB0 Q_OffsetRangeList__rsrpOffsetCSI_RS__dft_helper Q_OffsetRangeList__rsrpOffsetCSI_RS__dft_helper2 ::
 Dft Q_OffsetRange__Type Q_OffsetRange__cond Q_OffsetRange__dB0 Q_OffsetRangeList__rsrqOffsetCSI_RS__dft_helper Q_OffsetRangeList__rsrqOffsetCSI_RS__dft_helper2 ::
 Dft Q_OffsetRange__Type Q_OffsetRange__cond Q_OffsetRange__dB0 Q_OffsetRangeList__sinrOffsetCSI_RS__dft_helper Q_OffsetRangeList__sinrOffsetCSI_RS__dft_helper2 ::
 nil).
Definition Q_OffsetRangeList__cond z := 
  Q_OffsetRange__cond (Q_OffsetRangeList__rsrpOffsetSSB z) /\
  Q_OffsetRange__cond (Q_OffsetRangeList__rsrqOffsetSSB z) /\
  Q_OffsetRange__cond (Q_OffsetRangeList__sinrOffsetSSB z) /\
  Q_OffsetRange__cond (Q_OffsetRangeList__rsrpOffsetCSI_RS z) /\
  Q_OffsetRange__cond (Q_OffsetRangeList__rsrqOffsetCSI_RS z) /\
  Q_OffsetRange__cond (Q_OffsetRangeList__sinrOffsetCSI_RS z) /\
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

Definition Q_OffsetRangeList__Format_Type := Eval cbn in seq_format_prod Q_OffsetRangeList__list.
Definition Q_OffsetRangeList__Format_list : Q_OffsetRangeList__Format_Type :=
  (Q_OffsetRange__Format, (Q_OffsetRange__Format, (Q_OffsetRange__Format, (Q_OffsetRange__Format, (Q_OffsetRange__Format, (Q_OffsetRange__Format, unit_format)))))).
Definition Q_OffsetRangeList__list__Format := (*Eval compute in *) seq_format Q_OffsetRangeList__list Q_OffsetRangeList__Format_list.
Definition Q_OffsetRangeList__F1 z :=
  (Q_OffsetRangeList__rsrpOffsetSSB z, (Q_OffsetRangeList__rsrqOffsetSSB z, (Q_OffsetRangeList__sinrOffsetSSB z, (Q_OffsetRangeList__rsrpOffsetCSI_RS z, (Q_OffsetRangeList__rsrqOffsetCSI_RS z, (Q_OffsetRangeList__sinrOffsetCSI_RS z, tt)))))).
Definition Q_OffsetRangeList__F2 (y : seq_type Q_OffsetRangeList__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__Q_OffsetRangeList__Type i0 i1 i2 i3 i4 i5
  end.
Lemma Q_OffsetRangeList__F1F2_cond (z : Q_OffsetRangeList__Type)
  : Q_OffsetRangeList__cond z ->
  (seq_cond Q_OffsetRangeList__list (Q_OffsetRangeList__F1 z)).
intro H. unfold Q_OffsetRangeList__cond in H. simpl. auto. Qed.
Lemma Q_OffsetRangeList__F1F2_cond2 (z : Q_OffsetRangeList__Type)
 : Q_OffsetRangeList__F2 (Q_OffsetRangeList__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Q_OffsetRangeList__F2F1_cond (y : seq_type Q_OffsetRangeList__list)
  : seq_cond Q_OffsetRangeList__list y ->
 (Q_OffsetRangeList__cond (Q_OffsetRangeList__F2 y)) /\  Q_OffsetRangeList__F1 (Q_OffsetRangeList__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Q_OffsetRangeList__cond. simpl in *. auto.
 - simpl. unfold Q_OffsetRangeList__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Q_OffsetRangeList__Format : T_Format Q_OffsetRangeList__Type Q_OffsetRangeList__cond :=
        proj2_format  Q_OffsetRangeList__cond Q_OffsetRangeList__list__Format
    Q_OffsetRangeList__F1 Q_OffsetRangeList__F2 Q_OffsetRangeList__F1F2_cond  Q_OffsetRangeList__F1F2_cond2 Q_OffsetRangeList__F2F1_cond.
Opaque Q_OffsetRangeList__cond Q_OffsetRangeList__Format.

