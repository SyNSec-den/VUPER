Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.EUTRA_PhysCellId.

Opaque EUTRA_PhysCellId__cond EUTRA_PhysCellId__Format.

Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Record PCI_ARFCN_EUTRA_r16__Type : Set :=
  make__PCI_ARFCN_EUTRA_r16__Type {
    PCI_ARFCN_EUTRA_r16__physCellId_r16 : EUTRA_PhysCellId__Type ;
    PCI_ARFCN_EUTRA_r16__carrierFreq_r16 : ARFCN_ValueEUTRA__Type ;
}.
Definition PCI_ARFCN_EUTRA_r16__list := (
 Nor EUTRA_PhysCellId__Type EUTRA_PhysCellId__cond ::
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 nil).
Definition PCI_ARFCN_EUTRA_r16__cond z := 
  EUTRA_PhysCellId__cond (PCI_ARFCN_EUTRA_r16__physCellId_r16 z) /\
  ARFCN_ValueEUTRA__cond (PCI_ARFCN_EUTRA_r16__carrierFreq_r16 z) /\
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

Definition PCI_ARFCN_EUTRA_r16__Format_Type := Eval cbn in seq_format_prod PCI_ARFCN_EUTRA_r16__list.
Definition PCI_ARFCN_EUTRA_r16__Format_list : PCI_ARFCN_EUTRA_r16__Format_Type :=
  (EUTRA_PhysCellId__Format, (ARFCN_ValueEUTRA__Format, unit_format)).
Definition PCI_ARFCN_EUTRA_r16__list__Format := (*Eval compute in *) seq_format PCI_ARFCN_EUTRA_r16__list PCI_ARFCN_EUTRA_r16__Format_list.
Definition PCI_ARFCN_EUTRA_r16__F1 z :=
  (PCI_ARFCN_EUTRA_r16__physCellId_r16 z, (PCI_ARFCN_EUTRA_r16__carrierFreq_r16 z, tt)).
Definition PCI_ARFCN_EUTRA_r16__F2 (y : seq_type PCI_ARFCN_EUTRA_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PCI_ARFCN_EUTRA_r16__Type i0 i1
  end.
Lemma PCI_ARFCN_EUTRA_r16__F1F2_cond (z : PCI_ARFCN_EUTRA_r16__Type)
  : PCI_ARFCN_EUTRA_r16__cond z ->
  (seq_cond PCI_ARFCN_EUTRA_r16__list (PCI_ARFCN_EUTRA_r16__F1 z)).
intro H. unfold PCI_ARFCN_EUTRA_r16__cond in H. simpl. auto. Qed.
Lemma PCI_ARFCN_EUTRA_r16__F1F2_cond2 (z : PCI_ARFCN_EUTRA_r16__Type)
 : PCI_ARFCN_EUTRA_r16__F2 (PCI_ARFCN_EUTRA_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PCI_ARFCN_EUTRA_r16__F2F1_cond (y : seq_type PCI_ARFCN_EUTRA_r16__list)
  : seq_cond PCI_ARFCN_EUTRA_r16__list y ->
 (PCI_ARFCN_EUTRA_r16__cond (PCI_ARFCN_EUTRA_r16__F2 y)) /\  PCI_ARFCN_EUTRA_r16__F1 (PCI_ARFCN_EUTRA_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PCI_ARFCN_EUTRA_r16__cond. simpl in *. auto.
 - simpl. unfold PCI_ARFCN_EUTRA_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PCI_ARFCN_EUTRA_r16__Format : T_Format PCI_ARFCN_EUTRA_r16__Type PCI_ARFCN_EUTRA_r16__cond :=
        proj2_format  PCI_ARFCN_EUTRA_r16__cond PCI_ARFCN_EUTRA_r16__list__Format
    PCI_ARFCN_EUTRA_r16__F1 PCI_ARFCN_EUTRA_r16__F2 PCI_ARFCN_EUTRA_r16__F1F2_cond  PCI_ARFCN_EUTRA_r16__F1F2_cond2 PCI_ARFCN_EUTRA_r16__F2F1_cond.
Opaque PCI_ARFCN_EUTRA_r16__cond PCI_ARFCN_EUTRA_r16__Format.

