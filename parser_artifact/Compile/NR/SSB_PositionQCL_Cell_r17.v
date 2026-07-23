Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.SSB_PositionQCL_Relation_r17.

Opaque SSB_PositionQCL_Relation_r17__cond SSB_PositionQCL_Relation_r17__Format.

Record SSB_PositionQCL_Cell_r17__Type : Set :=
  make__SSB_PositionQCL_Cell_r17__Type {
    SSB_PositionQCL_Cell_r17__physCellId_r17 : PhysCellId__Type ;
    SSB_PositionQCL_Cell_r17__ssb_PositionQCL_r17 : SSB_PositionQCL_Relation_r17__Type ;
}.
Definition SSB_PositionQCL_Cell_r17__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor SSB_PositionQCL_Relation_r17__Type SSB_PositionQCL_Relation_r17__cond ::
 nil).
Definition SSB_PositionQCL_Cell_r17__cond z := 
  PhysCellId__cond (SSB_PositionQCL_Cell_r17__physCellId_r17 z) /\
  SSB_PositionQCL_Relation_r17__cond (SSB_PositionQCL_Cell_r17__ssb_PositionQCL_r17 z) /\
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

Definition SSB_PositionQCL_Cell_r17__Format_Type := Eval cbn in seq_format_prod SSB_PositionQCL_Cell_r17__list.
Definition SSB_PositionQCL_Cell_r17__Format_list : SSB_PositionQCL_Cell_r17__Format_Type :=
  (PhysCellId__Format, (SSB_PositionQCL_Relation_r17__Format, unit_format)).
Definition SSB_PositionQCL_Cell_r17__list__Format := (*Eval compute in *) seq_format SSB_PositionQCL_Cell_r17__list SSB_PositionQCL_Cell_r17__Format_list.
Definition SSB_PositionQCL_Cell_r17__F1 z :=
  (SSB_PositionQCL_Cell_r17__physCellId_r17 z, (SSB_PositionQCL_Cell_r17__ssb_PositionQCL_r17 z, tt)).
Definition SSB_PositionQCL_Cell_r17__F2 (y : seq_type SSB_PositionQCL_Cell_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SSB_PositionQCL_Cell_r17__Type i0 i1
  end.
Lemma SSB_PositionQCL_Cell_r17__F1F2_cond (z : SSB_PositionQCL_Cell_r17__Type)
  : SSB_PositionQCL_Cell_r17__cond z ->
  (seq_cond SSB_PositionQCL_Cell_r17__list (SSB_PositionQCL_Cell_r17__F1 z)).
intro H. unfold SSB_PositionQCL_Cell_r17__cond in H. simpl. auto. Qed.
Lemma SSB_PositionQCL_Cell_r17__F1F2_cond2 (z : SSB_PositionQCL_Cell_r17__Type)
 : SSB_PositionQCL_Cell_r17__F2 (SSB_PositionQCL_Cell_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_PositionQCL_Cell_r17__F2F1_cond (y : seq_type SSB_PositionQCL_Cell_r17__list)
  : seq_cond SSB_PositionQCL_Cell_r17__list y ->
 (SSB_PositionQCL_Cell_r17__cond (SSB_PositionQCL_Cell_r17__F2 y)) /\  SSB_PositionQCL_Cell_r17__F1 (SSB_PositionQCL_Cell_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_PositionQCL_Cell_r17__cond. simpl in *. auto.
 - simpl. unfold SSB_PositionQCL_Cell_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_PositionQCL_Cell_r17__Format : T_Format SSB_PositionQCL_Cell_r17__Type SSB_PositionQCL_Cell_r17__cond :=
        proj2_format  SSB_PositionQCL_Cell_r17__cond SSB_PositionQCL_Cell_r17__list__Format
    SSB_PositionQCL_Cell_r17__F1 SSB_PositionQCL_Cell_r17__F2 SSB_PositionQCL_Cell_r17__F1F2_cond  SSB_PositionQCL_Cell_r17__F1F2_cond2 SSB_PositionQCL_Cell_r17__F2F1_cond.
Opaque SSB_PositionQCL_Cell_r17__cond SSB_PositionQCL_Cell_r17__Format.

