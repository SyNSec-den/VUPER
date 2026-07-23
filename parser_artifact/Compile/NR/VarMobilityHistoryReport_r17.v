Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.VisitedCellInfoList_r16.

Opaque VisitedCellInfoList_r16__cond VisitedCellInfoList_r16__Format.

Require Import NR.VisitedPSCellInfoList_r17.

Opaque VisitedPSCellInfoList_r17__cond VisitedPSCellInfoList_r17__Format.

Record VarMobilityHistoryReport_r17__Type : Set :=
  make__VarMobilityHistoryReport_r17__Type {
    VarMobilityHistoryReport_r17__visitedCellInfoList_r16 : VisitedCellInfoList_r16__Type ;
    VarMobilityHistoryReport_r17__visitedPSCellInfoListReport_r17 : option VisitedPSCellInfoList_r17__Type ;
}.
Definition VarMobilityHistoryReport_r17__list := (
 Nor VisitedCellInfoList_r16__Type VisitedCellInfoList_r16__cond ::
 Opt VisitedPSCellInfoList_r17__Type VisitedPSCellInfoList_r17__cond ::
 nil).
Definition VarMobilityHistoryReport_r17__cond z := 
  VisitedCellInfoList_r16__cond (VarMobilityHistoryReport_r17__visitedCellInfoList_r16 z) /\
  opt_cond VisitedPSCellInfoList_r17__cond (VarMobilityHistoryReport_r17__visitedPSCellInfoListReport_r17 z) /\
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

Definition VarMobilityHistoryReport_r17__Format_Type := Eval cbn in seq_format_prod VarMobilityHistoryReport_r17__list.
Definition VarMobilityHistoryReport_r17__Format_list : VarMobilityHistoryReport_r17__Format_Type :=
  (VisitedCellInfoList_r16__Format, (VisitedPSCellInfoList_r17__Format, unit_format)).
Definition VarMobilityHistoryReport_r17__list__Format := (*Eval compute in *) seq_format VarMobilityHistoryReport_r17__list VarMobilityHistoryReport_r17__Format_list.
Definition VarMobilityHistoryReport_r17__F1 z :=
  (VarMobilityHistoryReport_r17__visitedCellInfoList_r16 z, (VarMobilityHistoryReport_r17__visitedPSCellInfoListReport_r17 z, tt)).
Definition VarMobilityHistoryReport_r17__F2 (y : seq_type VarMobilityHistoryReport_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__VarMobilityHistoryReport_r17__Type i0 i1
  end.
Lemma VarMobilityHistoryReport_r17__F1F2_cond (z : VarMobilityHistoryReport_r17__Type)
  : VarMobilityHistoryReport_r17__cond z ->
  (seq_cond VarMobilityHistoryReport_r17__list (VarMobilityHistoryReport_r17__F1 z)).
intro H. unfold VarMobilityHistoryReport_r17__cond in H. simpl. auto. Qed.
Lemma VarMobilityHistoryReport_r17__F1F2_cond2 (z : VarMobilityHistoryReport_r17__Type)
 : VarMobilityHistoryReport_r17__F2 (VarMobilityHistoryReport_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarMobilityHistoryReport_r17__F2F1_cond (y : seq_type VarMobilityHistoryReport_r17__list)
  : seq_cond VarMobilityHistoryReport_r17__list y ->
 (VarMobilityHistoryReport_r17__cond (VarMobilityHistoryReport_r17__F2 y)) /\  VarMobilityHistoryReport_r17__F1 (VarMobilityHistoryReport_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarMobilityHistoryReport_r17__cond. simpl in *. auto.
 - simpl. unfold VarMobilityHistoryReport_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarMobilityHistoryReport_r17__Format : T_Format VarMobilityHistoryReport_r17__Type VarMobilityHistoryReport_r17__cond :=
        proj2_format  VarMobilityHistoryReport_r17__cond VarMobilityHistoryReport_r17__list__Format
    VarMobilityHistoryReport_r17__F1 VarMobilityHistoryReport_r17__F2 VarMobilityHistoryReport_r17__F1F2_cond  VarMobilityHistoryReport_r17__F1F2_cond2 VarMobilityHistoryReport_r17__F2F1_cond.
Opaque VarMobilityHistoryReport_r17__cond VarMobilityHistoryReport_r17__Format.

