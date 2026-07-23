Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Type : Set :=
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms0dot5
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms1
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms2
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms3
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms4
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms5
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms6
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms7
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms8
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms9
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms10
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare5
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare4
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare3
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare2
 | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare1
.
Definition PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__cond := (fun (_ : PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Type) => True).
Lemma PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__nat__helper.

Definition PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F1 t :=
  match t with
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms0dot5 => 0
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms1 => 1
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms2 => 2
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms3 => 3
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms4 => 4
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms5 => 5
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms6 => 6
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms7 => 7
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms8 => 8
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms9 => 9
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms10 => 10
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare5 => 11
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare4 => 12
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare3 => 13
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare2 => 14
  | PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare1 => 15
  end.
Definition PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F2 n :=
  match n with
  | 0 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms0dot5
  | 1 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms1
  | 2 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms2
  | 3 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms3
  | 4 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms4
  | 5 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms5
  | 6 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms6
  | 7 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms7
  | 8 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms8
  | 9 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms9
  | 10 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms10
  | 11 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare5
  | 12 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare4
  | 13 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare3
  | 14 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare2
  | 15 => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__spare1
  | _ => PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__ms0dot5
  end.
Lemma PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F1F2 : forall x : PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Type, (PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F1 x <= 15) /\ PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F2 (PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F1 x) = x. imp_solve. Qed.
Lemma PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F2F1 : forall (y : nat) (H : y <= 15), PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F1 (PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.NeighbourCellInfo_r17.

Opaque NeighbourCellInfo_r17__cond NeighbourCellInfo_r17__Format.

Definition PropDelayDiffReportConfig_r17__neighCellInfoList_r17__Type := list NeighbourCellInfo_r17__Type.

Lemma PropDelayDiffReportConfig_r17__neighCellInfoList_r17__helper1 : (0 <= 1 <= maxCellNTN_r17)%Z. unfold maxCellNTN_r17.
 lia. Qed.
Lemma PropDelayDiffReportConfig_r17__neighCellInfoList_r17__helper2 : to_bit_sz (Z.to_nat (maxCellNTN_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellNTN_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PropDelayDiffReportConfig_r17__neighCellInfoList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PropDelayDiffReportConfig_r17__neighCellInfoList_r17__cond (z : PropDelayDiffReportConfig_r17__neighCellInfoList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxCellNTN_r17)%Z /\ (list_and NeighbourCellInfo_r17__cond z) .

Record PropDelayDiffReportConfig_r17__Type : Set :=
  make__PropDelayDiffReportConfig_r17__Type {
    PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17 : option PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Type ;
    PropDelayDiffReportConfig_r17__neighCellInfoList_r17 : option PropDelayDiffReportConfig_r17__neighCellInfoList_r17__Type ;
}.
Definition PropDelayDiffReportConfig_r17__list := (
 Opt PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Type PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__cond ::
 Opt PropDelayDiffReportConfig_r17__neighCellInfoList_r17__Type PropDelayDiffReportConfig_r17__neighCellInfoList_r17__cond ::
 nil).
Definition PropDelayDiffReportConfig_r17__cond z := 
  opt_cond PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__cond (PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17 z) /\
  opt_cond PropDelayDiffReportConfig_r17__neighCellInfoList_r17__cond (PropDelayDiffReportConfig_r17__neighCellInfoList_r17 z) /\
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
Definition PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Format : T_Format PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__nat__Format PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F1 PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F2 PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F1F2 PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__F2F1.

Opaque PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__cond PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Format.

Definition PropDelayDiffReportConfig_r17__neighCellInfoList_r17__Format : T_Format PropDelayDiffReportConfig_r17__neighCellInfoList_r17__Type PropDelayDiffReportConfig_r17__neighCellInfoList_r17__cond := seq_of_format NeighbourCellInfo_r17__Format 1 maxCellNTN_r17 PropDelayDiffReportConfig_r17__neighCellInfoList_r17__helper1 PropDelayDiffReportConfig_r17__neighCellInfoList_r17__helper2.

Opaque PropDelayDiffReportConfig_r17__neighCellInfoList_r17__cond PropDelayDiffReportConfig_r17__neighCellInfoList_r17__Format.


Definition PropDelayDiffReportConfig_r17__Format_Type := Eval cbn in seq_format_prod PropDelayDiffReportConfig_r17__list.
Definition PropDelayDiffReportConfig_r17__Format_list : PropDelayDiffReportConfig_r17__Format_Type :=
  (PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17__Format, (PropDelayDiffReportConfig_r17__neighCellInfoList_r17__Format, unit_format)).
Definition PropDelayDiffReportConfig_r17__list__Format := (*Eval compute in *) seq_format PropDelayDiffReportConfig_r17__list PropDelayDiffReportConfig_r17__Format_list.
Definition PropDelayDiffReportConfig_r17__F1 z :=
  (PropDelayDiffReportConfig_r17__threshPropDelayDiff_r17 z, (PropDelayDiffReportConfig_r17__neighCellInfoList_r17 z, tt)).
Definition PropDelayDiffReportConfig_r17__F2 (y : seq_type PropDelayDiffReportConfig_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PropDelayDiffReportConfig_r17__Type i0 i1
  end.
Lemma PropDelayDiffReportConfig_r17__F1F2_cond (z : PropDelayDiffReportConfig_r17__Type)
  : PropDelayDiffReportConfig_r17__cond z ->
  (seq_cond PropDelayDiffReportConfig_r17__list (PropDelayDiffReportConfig_r17__F1 z)).
intro H. unfold PropDelayDiffReportConfig_r17__cond in H. simpl. auto. Qed.
Lemma PropDelayDiffReportConfig_r17__F1F2_cond2 (z : PropDelayDiffReportConfig_r17__Type)
 : PropDelayDiffReportConfig_r17__F2 (PropDelayDiffReportConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PropDelayDiffReportConfig_r17__F2F1_cond (y : seq_type PropDelayDiffReportConfig_r17__list)
  : seq_cond PropDelayDiffReportConfig_r17__list y ->
 (PropDelayDiffReportConfig_r17__cond (PropDelayDiffReportConfig_r17__F2 y)) /\  PropDelayDiffReportConfig_r17__F1 (PropDelayDiffReportConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PropDelayDiffReportConfig_r17__cond. simpl in *. auto.
 - simpl. unfold PropDelayDiffReportConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PropDelayDiffReportConfig_r17__Format : T_Format PropDelayDiffReportConfig_r17__Type PropDelayDiffReportConfig_r17__cond :=
        proj2_format  PropDelayDiffReportConfig_r17__cond PropDelayDiffReportConfig_r17__list__Format
    PropDelayDiffReportConfig_r17__F1 PropDelayDiffReportConfig_r17__F2 PropDelayDiffReportConfig_r17__F1F2_cond  PropDelayDiffReportConfig_r17__F1F2_cond2 PropDelayDiffReportConfig_r17__F2F1_cond.
Opaque PropDelayDiffReportConfig_r17__cond PropDelayDiffReportConfig_r17__Format.

