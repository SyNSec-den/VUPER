Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Type : Set :=
 | MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__supported
.
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__cond := (fun (_ : MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Type) => True).
Lemma MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__nat__helper.

Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F1 t :=
  match t with
  | MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__supported => 0
  end.
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F2 n :=
  match n with
  | 0 => MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__supported
  | _ => MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__supported
  end.
Lemma MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F1F2 : forall x : MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Type, (MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F1 x <= 0) /\ MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F2 (MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F1 (MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersMRDC_XDD_Diff_v1560__Type : Set :=
  make__MeasAndMobParametersMRDC_XDD_Diff_v1560__Type {
    MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC : option MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Type ;
}.
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__list := (
 Opt MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Type MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__cond ::
 nil).
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__cond z := 
  opt_cond MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__cond (MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC z) /\
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
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Format : T_Format MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__nat__Format MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F1 MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F2 MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F1F2 MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__F2F1.

Opaque MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__cond MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Format.


Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersMRDC_XDD_Diff_v1560__list.
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__Format_list : MeasAndMobParametersMRDC_XDD_Diff_v1560__Format_Type :=
  (MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC__Format, unit_format).
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersMRDC_XDD_Diff_v1560__list MeasAndMobParametersMRDC_XDD_Diff_v1560__Format_list.
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__F1 z :=
  (MeasAndMobParametersMRDC_XDD_Diff_v1560__sftd_MeasPSCell_NEDC z, tt).
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__F2 (y : seq_type MeasAndMobParametersMRDC_XDD_Diff_v1560__list) :=
  match y with
  | (i0, _)=>
    make__MeasAndMobParametersMRDC_XDD_Diff_v1560__Type i0
  end.
Lemma MeasAndMobParametersMRDC_XDD_Diff_v1560__F1F2_cond (z : MeasAndMobParametersMRDC_XDD_Diff_v1560__Type)
  : MeasAndMobParametersMRDC_XDD_Diff_v1560__cond z ->
  (seq_cond MeasAndMobParametersMRDC_XDD_Diff_v1560__list (MeasAndMobParametersMRDC_XDD_Diff_v1560__F1 z)).
intro H. unfold MeasAndMobParametersMRDC_XDD_Diff_v1560__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersMRDC_XDD_Diff_v1560__F1F2_cond2 (z : MeasAndMobParametersMRDC_XDD_Diff_v1560__Type)
 : MeasAndMobParametersMRDC_XDD_Diff_v1560__F2 (MeasAndMobParametersMRDC_XDD_Diff_v1560__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersMRDC_XDD_Diff_v1560__F2F1_cond (y : seq_type MeasAndMobParametersMRDC_XDD_Diff_v1560__list)
  : seq_cond MeasAndMobParametersMRDC_XDD_Diff_v1560__list y ->
 (MeasAndMobParametersMRDC_XDD_Diff_v1560__cond (MeasAndMobParametersMRDC_XDD_Diff_v1560__F2 y)) /\  MeasAndMobParametersMRDC_XDD_Diff_v1560__F1 (MeasAndMobParametersMRDC_XDD_Diff_v1560__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersMRDC_XDD_Diff_v1560__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersMRDC_XDD_Diff_v1560__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersMRDC_XDD_Diff_v1560__Format : T_Format MeasAndMobParametersMRDC_XDD_Diff_v1560__Type MeasAndMobParametersMRDC_XDD_Diff_v1560__cond :=
        proj2_format  MeasAndMobParametersMRDC_XDD_Diff_v1560__cond MeasAndMobParametersMRDC_XDD_Diff_v1560__list__Format
    MeasAndMobParametersMRDC_XDD_Diff_v1560__F1 MeasAndMobParametersMRDC_XDD_Diff_v1560__F2 MeasAndMobParametersMRDC_XDD_Diff_v1560__F1F2_cond  MeasAndMobParametersMRDC_XDD_Diff_v1560__F1F2_cond2 MeasAndMobParametersMRDC_XDD_Diff_v1560__F2F1_cond.
Opaque MeasAndMobParametersMRDC_XDD_Diff_v1560__cond MeasAndMobParametersMRDC_XDD_Diff_v1560__Format.

