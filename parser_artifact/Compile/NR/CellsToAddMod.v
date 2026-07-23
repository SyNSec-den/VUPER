Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.Q_OffsetRangeList.

Opaque Q_OffsetRangeList__cond Q_OffsetRangeList__Format.

Record CellsToAddMod__Type : Set :=
  make__CellsToAddMod__Type {
    CellsToAddMod__physCellId : PhysCellId__Type ;
    CellsToAddMod__cellIndividualOffset : Q_OffsetRangeList__Type ;
}.
Definition CellsToAddMod__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor Q_OffsetRangeList__Type Q_OffsetRangeList__cond ::
 nil).
Definition CellsToAddMod__cond z := 
  PhysCellId__cond (CellsToAddMod__physCellId z) /\
  Q_OffsetRangeList__cond (CellsToAddMod__cellIndividualOffset z) /\
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

Definition CellsToAddMod__Format_Type := Eval cbn in seq_format_prod CellsToAddMod__list.
Definition CellsToAddMod__Format_list : CellsToAddMod__Format_Type :=
  (PhysCellId__Format, (Q_OffsetRangeList__Format, unit_format)).
Definition CellsToAddMod__list__Format := (*Eval compute in *) seq_format CellsToAddMod__list CellsToAddMod__Format_list.
Definition CellsToAddMod__F1 z :=
  (CellsToAddMod__physCellId z, (CellsToAddMod__cellIndividualOffset z, tt)).
Definition CellsToAddMod__F2 (y : seq_type CellsToAddMod__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CellsToAddMod__Type i0 i1
  end.
Lemma CellsToAddMod__F1F2_cond (z : CellsToAddMod__Type)
  : CellsToAddMod__cond z ->
  (seq_cond CellsToAddMod__list (CellsToAddMod__F1 z)).
intro H. unfold CellsToAddMod__cond in H. simpl. auto. Qed.
Lemma CellsToAddMod__F1F2_cond2 (z : CellsToAddMod__Type)
 : CellsToAddMod__F2 (CellsToAddMod__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellsToAddMod__F2F1_cond (y : seq_type CellsToAddMod__list)
  : seq_cond CellsToAddMod__list y ->
 (CellsToAddMod__cond (CellsToAddMod__F2 y)) /\  CellsToAddMod__F1 (CellsToAddMod__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellsToAddMod__cond. simpl in *. auto.
 - simpl. unfold CellsToAddMod__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellsToAddMod__Format : T_Format CellsToAddMod__Type CellsToAddMod__cond :=
        proj2_format  CellsToAddMod__cond CellsToAddMod__list__Format
    CellsToAddMod__F1 CellsToAddMod__F2 CellsToAddMod__F1F2_cond  CellsToAddMod__F1F2_cond2 CellsToAddMod__F2F1_cond.
Opaque CellsToAddMod__cond CellsToAddMod__Format.

