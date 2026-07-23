Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Record MeasReportQuantity__Type : Set :=
  make__MeasReportQuantity__Type {
    MeasReportQuantity__rsrp : bool ;
    MeasReportQuantity__rsrq : bool ;
    MeasReportQuantity__sinr : bool ;
}.
Definition MeasReportQuantity__list := (
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 nil).
Definition MeasReportQuantity__cond z := 
  (fun _ => True) (MeasReportQuantity__rsrp z) /\
  (fun _ => True) (MeasReportQuantity__rsrq z) /\
  (fun _ => True) (MeasReportQuantity__sinr z) /\
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

Definition MeasReportQuantity__Format_Type := Eval cbn in seq_format_prod MeasReportQuantity__list.
Definition MeasReportQuantity__Format_list : MeasReportQuantity__Format_Type :=
  (bool__Format, (bool__Format, (bool__Format, unit_format))).
Definition MeasReportQuantity__list__Format := (*Eval compute in *) seq_format MeasReportQuantity__list MeasReportQuantity__Format_list.
Definition MeasReportQuantity__F1 z :=
  (MeasReportQuantity__rsrp z, (MeasReportQuantity__rsrq z, (MeasReportQuantity__sinr z, tt))).
Definition MeasReportQuantity__F2 (y : seq_type MeasReportQuantity__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasReportQuantity__Type i0 i1 i2
  end.
Lemma MeasReportQuantity__F1F2_cond (z : MeasReportQuantity__Type)
  : MeasReportQuantity__cond z ->
  (seq_cond MeasReportQuantity__list (MeasReportQuantity__F1 z)).
intro H. unfold MeasReportQuantity__cond in H. simpl. auto. Qed.
Lemma MeasReportQuantity__F1F2_cond2 (z : MeasReportQuantity__Type)
 : MeasReportQuantity__F2 (MeasReportQuantity__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasReportQuantity__F2F1_cond (y : seq_type MeasReportQuantity__list)
  : seq_cond MeasReportQuantity__list y ->
 (MeasReportQuantity__cond (MeasReportQuantity__F2 y)) /\  MeasReportQuantity__F1 (MeasReportQuantity__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasReportQuantity__cond. simpl in *. auto.
 - simpl. unfold MeasReportQuantity__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasReportQuantity__Format : T_Format MeasReportQuantity__Type MeasReportQuantity__cond :=
        proj2_format  MeasReportQuantity__cond MeasReportQuantity__list__Format
    MeasReportQuantity__F1 MeasReportQuantity__F2 MeasReportQuantity__F1F2_cond  MeasReportQuantity__F1F2_cond2 MeasReportQuantity__F2F1_cond.
Opaque MeasReportQuantity__cond MeasReportQuantity__Format.

