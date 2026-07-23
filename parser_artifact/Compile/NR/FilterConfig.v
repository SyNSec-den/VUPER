Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FilterCoefficient.

Opaque FilterCoefficient__cond FilterCoefficient__Format.

Definition FilterConfig__filterCoefficientRSRP__dft_helper : FilterCoefficient__cond (inl FilterCoefficient__root__fc4). apply I. Qed.
Require Import Coq.Logic.ProofIrrelevance.
Definition FilterConfig__filterCoefficientRSRP__dft_helper2 : forall (x y : FilterCoefficient__Type), {x = y} + {x <> y}.
decide equality.
             - (decide equality).
             - destruct b, f. Defined.
Require Import NR.FilterCoefficient.

Opaque FilterCoefficient__cond FilterCoefficient__Format.

Definition FilterConfig__filterCoefficientRSRQ__dft_helper : FilterCoefficient__cond (inl FilterCoefficient__root__fc4). apply I. Qed.
Require Import Coq.Logic.ProofIrrelevance.
Definition FilterConfig__filterCoefficientRSRQ__dft_helper2 : forall (x y : FilterCoefficient__Type), {x = y} + {x <> y}.
decide equality.
             - (decide equality).
             - destruct b, f. Defined.
Require Import NR.FilterCoefficient.

Opaque FilterCoefficient__cond FilterCoefficient__Format.

Definition FilterConfig__filterCoefficientRS_SINR__dft_helper : FilterCoefficient__cond (inl FilterCoefficient__root__fc4). apply I. Qed.
Require Import Coq.Logic.ProofIrrelevance.
Definition FilterConfig__filterCoefficientRS_SINR__dft_helper2 : forall (x y : FilterCoefficient__Type), {x = y} + {x <> y}.
decide equality.
             - (decide equality).
             - destruct b, f. Defined.
Record FilterConfig__Type : Set :=
  make__FilterConfig__Type {
    FilterConfig__filterCoefficientRSRP : FilterCoefficient__Type ;
    FilterConfig__filterCoefficientRSRQ : FilterCoefficient__Type ;
    FilterConfig__filterCoefficientRS_SINR : FilterCoefficient__Type ;
}.
Definition FilterConfig__list := (
 Dft FilterCoefficient__Type FilterCoefficient__cond (inl FilterCoefficient__root__fc4) FilterConfig__filterCoefficientRSRP__dft_helper FilterConfig__filterCoefficientRSRP__dft_helper2 ::
 Dft FilterCoefficient__Type FilterCoefficient__cond (inl FilterCoefficient__root__fc4) FilterConfig__filterCoefficientRSRQ__dft_helper FilterConfig__filterCoefficientRSRQ__dft_helper2 ::
 Dft FilterCoefficient__Type FilterCoefficient__cond (inl FilterCoefficient__root__fc4) FilterConfig__filterCoefficientRS_SINR__dft_helper FilterConfig__filterCoefficientRS_SINR__dft_helper2 ::
 nil).
Definition FilterConfig__cond z := 
  FilterCoefficient__cond (FilterConfig__filterCoefficientRSRP z) /\
  FilterCoefficient__cond (FilterConfig__filterCoefficientRSRQ z) /\
  FilterCoefficient__cond (FilterConfig__filterCoefficientRS_SINR z) /\
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

Definition FilterConfig__Format_Type := Eval cbn in seq_format_prod FilterConfig__list.
Definition FilterConfig__Format_list : FilterConfig__Format_Type :=
  (FilterCoefficient__Format, (FilterCoefficient__Format, (FilterCoefficient__Format, unit_format))).
Definition FilterConfig__list__Format := (*Eval compute in *) seq_format FilterConfig__list FilterConfig__Format_list.
Definition FilterConfig__F1 z :=
  (FilterConfig__filterCoefficientRSRP z, (FilterConfig__filterCoefficientRSRQ z, (FilterConfig__filterCoefficientRS_SINR z, tt))).
Definition FilterConfig__F2 (y : seq_type FilterConfig__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FilterConfig__Type i0 i1 i2
  end.
Lemma FilterConfig__F1F2_cond (z : FilterConfig__Type)
  : FilterConfig__cond z ->
  (seq_cond FilterConfig__list (FilterConfig__F1 z)).
intro H. unfold FilterConfig__cond in H. simpl. auto. Qed.
Lemma FilterConfig__F1F2_cond2 (z : FilterConfig__Type)
 : FilterConfig__F2 (FilterConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FilterConfig__F2F1_cond (y : seq_type FilterConfig__list)
  : seq_cond FilterConfig__list y ->
 (FilterConfig__cond (FilterConfig__F2 y)) /\  FilterConfig__F1 (FilterConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FilterConfig__cond. simpl in *. auto.
 - simpl. unfold FilterConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FilterConfig__Format : T_Format FilterConfig__Type FilterConfig__cond :=
        proj2_format  FilterConfig__cond FilterConfig__list__Format
    FilterConfig__F1 FilterConfig__F2 FilterConfig__F1F2_cond  FilterConfig__F1F2_cond2 FilterConfig__F2F1_cond.
Opaque FilterConfig__cond FilterConfig__Format.

