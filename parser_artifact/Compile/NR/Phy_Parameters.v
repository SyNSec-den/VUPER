Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.Phy_ParametersCommon.

Opaque Phy_ParametersCommon__cond Phy_ParametersCommon__Format.

Require Import NR.Phy_ParametersXDD_Diff.

Opaque Phy_ParametersXDD_Diff__cond Phy_ParametersXDD_Diff__Format.

Require Import NR.Phy_ParametersFRX_Diff.

Opaque Phy_ParametersFRX_Diff__cond Phy_ParametersFRX_Diff__Format.

Require Import NR.Phy_ParametersFR1.

Opaque Phy_ParametersFR1__cond Phy_ParametersFR1__Format.

Require Import NR.Phy_ParametersFR2.

Opaque Phy_ParametersFR2__cond Phy_ParametersFR2__Format.

Record Phy_Parameters__Type : Set :=
  make__Phy_Parameters__Type {
    Phy_Parameters__phy_ParametersCommon : option Phy_ParametersCommon__Type ;
    Phy_Parameters__phy_ParametersXDD_Diff : option Phy_ParametersXDD_Diff__Type ;
    Phy_Parameters__phy_ParametersFRX_Diff : option Phy_ParametersFRX_Diff__Type ;
    Phy_Parameters__phy_ParametersFR1 : option Phy_ParametersFR1__Type ;
    Phy_Parameters__phy_ParametersFR2 : option Phy_ParametersFR2__Type ;
}.
Definition Phy_Parameters__list := (
 Opt Phy_ParametersCommon__Type Phy_ParametersCommon__cond ::
 Opt Phy_ParametersXDD_Diff__Type Phy_ParametersXDD_Diff__cond ::
 Opt Phy_ParametersFRX_Diff__Type Phy_ParametersFRX_Diff__cond ::
 Opt Phy_ParametersFR1__Type Phy_ParametersFR1__cond ::
 Opt Phy_ParametersFR2__Type Phy_ParametersFR2__cond ::
 nil).
Definition Phy_Parameters__cond z := 
  opt_cond Phy_ParametersCommon__cond (Phy_Parameters__phy_ParametersCommon z) /\
  opt_cond Phy_ParametersXDD_Diff__cond (Phy_Parameters__phy_ParametersXDD_Diff z) /\
  opt_cond Phy_ParametersFRX_Diff__cond (Phy_Parameters__phy_ParametersFRX_Diff z) /\
  opt_cond Phy_ParametersFR1__cond (Phy_Parameters__phy_ParametersFR1 z) /\
  opt_cond Phy_ParametersFR2__cond (Phy_Parameters__phy_ParametersFR2 z) /\
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

Definition Phy_Parameters__Format_Type := Eval cbn in seq_format_prod Phy_Parameters__list.
Definition Phy_Parameters__Format_list : Phy_Parameters__Format_Type :=
  (Phy_ParametersCommon__Format, (Phy_ParametersXDD_Diff__Format, (Phy_ParametersFRX_Diff__Format, (Phy_ParametersFR1__Format, (Phy_ParametersFR2__Format, unit_format))))).
Definition Phy_Parameters__list__Format := (*Eval compute in *) seq_format Phy_Parameters__list Phy_Parameters__Format_list.
Definition Phy_Parameters__F1 z :=
  (Phy_Parameters__phy_ParametersCommon z, (Phy_Parameters__phy_ParametersXDD_Diff z, (Phy_Parameters__phy_ParametersFRX_Diff z, (Phy_Parameters__phy_ParametersFR1 z, (Phy_Parameters__phy_ParametersFR2 z, tt))))).
Definition Phy_Parameters__F2 (y : seq_type Phy_Parameters__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__Phy_Parameters__Type i0 i1 i2 i3 i4
  end.
Lemma Phy_Parameters__F1F2_cond (z : Phy_Parameters__Type)
  : Phy_Parameters__cond z ->
  (seq_cond Phy_Parameters__list (Phy_Parameters__F1 z)).
intro H. unfold Phy_Parameters__cond in H. simpl. auto. Qed.
Lemma Phy_Parameters__F1F2_cond2 (z : Phy_Parameters__Type)
 : Phy_Parameters__F2 (Phy_Parameters__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_Parameters__F2F1_cond (y : seq_type Phy_Parameters__list)
  : seq_cond Phy_Parameters__list y ->
 (Phy_Parameters__cond (Phy_Parameters__F2 y)) /\  Phy_Parameters__F1 (Phy_Parameters__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_Parameters__cond. simpl in *. auto.
 - simpl. unfold Phy_Parameters__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_Parameters__Format : T_Format Phy_Parameters__Type Phy_Parameters__cond :=
        proj2_format  Phy_Parameters__cond Phy_Parameters__list__Format
    Phy_Parameters__F1 Phy_Parameters__F2 Phy_Parameters__F1F2_cond  Phy_Parameters__F1F2_cond2 Phy_Parameters__F2F1_cond.
Opaque Phy_Parameters__cond Phy_Parameters__Format.

