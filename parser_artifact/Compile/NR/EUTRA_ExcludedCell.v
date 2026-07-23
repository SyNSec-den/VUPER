Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EUTRA_CellIndex.

Opaque EUTRA_CellIndex__cond EUTRA_CellIndex__Format.

Require Import NR.EUTRA_PhysCellIdRange.

Opaque EUTRA_PhysCellIdRange__cond EUTRA_PhysCellIdRange__Format.

Record EUTRA_ExcludedCell__Type : Set :=
  make__EUTRA_ExcludedCell__Type {
    EUTRA_ExcludedCell__cellIndexEUTRA : EUTRA_CellIndex__Type ;
    EUTRA_ExcludedCell__physCellIdRange : EUTRA_PhysCellIdRange__Type ;
}.
Definition EUTRA_ExcludedCell__list := (
 Nor EUTRA_CellIndex__Type EUTRA_CellIndex__cond ::
 Nor EUTRA_PhysCellIdRange__Type EUTRA_PhysCellIdRange__cond ::
 nil).
Definition EUTRA_ExcludedCell__cond z := 
  EUTRA_CellIndex__cond (EUTRA_ExcludedCell__cellIndexEUTRA z) /\
  EUTRA_PhysCellIdRange__cond (EUTRA_ExcludedCell__physCellIdRange z) /\
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

Definition EUTRA_ExcludedCell__Format_Type := Eval cbn in seq_format_prod EUTRA_ExcludedCell__list.
Definition EUTRA_ExcludedCell__Format_list : EUTRA_ExcludedCell__Format_Type :=
  (EUTRA_CellIndex__Format, (EUTRA_PhysCellIdRange__Format, unit_format)).
Definition EUTRA_ExcludedCell__list__Format := (*Eval compute in *) seq_format EUTRA_ExcludedCell__list EUTRA_ExcludedCell__Format_list.
Definition EUTRA_ExcludedCell__F1 z :=
  (EUTRA_ExcludedCell__cellIndexEUTRA z, (EUTRA_ExcludedCell__physCellIdRange z, tt)).
Definition EUTRA_ExcludedCell__F2 (y : seq_type EUTRA_ExcludedCell__list) :=
  match y with
  | (i0, (i1, _))=>
    make__EUTRA_ExcludedCell__Type i0 i1
  end.
Lemma EUTRA_ExcludedCell__F1F2_cond (z : EUTRA_ExcludedCell__Type)
  : EUTRA_ExcludedCell__cond z ->
  (seq_cond EUTRA_ExcludedCell__list (EUTRA_ExcludedCell__F1 z)).
intro H. unfold EUTRA_ExcludedCell__cond in H. simpl. auto. Qed.
Lemma EUTRA_ExcludedCell__F1F2_cond2 (z : EUTRA_ExcludedCell__Type)
 : EUTRA_ExcludedCell__F2 (EUTRA_ExcludedCell__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EUTRA_ExcludedCell__F2F1_cond (y : seq_type EUTRA_ExcludedCell__list)
  : seq_cond EUTRA_ExcludedCell__list y ->
 (EUTRA_ExcludedCell__cond (EUTRA_ExcludedCell__F2 y)) /\  EUTRA_ExcludedCell__F1 (EUTRA_ExcludedCell__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EUTRA_ExcludedCell__cond. simpl in *. auto.
 - simpl. unfold EUTRA_ExcludedCell__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EUTRA_ExcludedCell__Format : T_Format EUTRA_ExcludedCell__Type EUTRA_ExcludedCell__cond :=
        proj2_format  EUTRA_ExcludedCell__cond EUTRA_ExcludedCell__list__Format
    EUTRA_ExcludedCell__F1 EUTRA_ExcludedCell__F2 EUTRA_ExcludedCell__F1F2_cond  EUTRA_ExcludedCell__F1F2_cond2 EUTRA_ExcludedCell__F2F1_cond.
Opaque EUTRA_ExcludedCell__cond EUTRA_ExcludedCell__Format.

