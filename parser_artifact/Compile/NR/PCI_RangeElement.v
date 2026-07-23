Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PCI_RangeIndex.

Opaque PCI_RangeIndex__cond PCI_RangeIndex__Format.

Require Import NR.PCI_Range.

Opaque PCI_Range__cond PCI_Range__Format.

Record PCI_RangeElement__Type : Set :=
  make__PCI_RangeElement__Type {
    PCI_RangeElement__pci_RangeIndex : PCI_RangeIndex__Type ;
    PCI_RangeElement__pci_Range : PCI_Range__Type ;
}.
Definition PCI_RangeElement__list := (
 Nor PCI_RangeIndex__Type PCI_RangeIndex__cond ::
 Nor PCI_Range__Type PCI_Range__cond ::
 nil).
Definition PCI_RangeElement__cond z := 
  PCI_RangeIndex__cond (PCI_RangeElement__pci_RangeIndex z) /\
  PCI_Range__cond (PCI_RangeElement__pci_Range z) /\
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

Definition PCI_RangeElement__Format_Type := Eval cbn in seq_format_prod PCI_RangeElement__list.
Definition PCI_RangeElement__Format_list : PCI_RangeElement__Format_Type :=
  (PCI_RangeIndex__Format, (PCI_Range__Format, unit_format)).
Definition PCI_RangeElement__list__Format := (*Eval compute in *) seq_format PCI_RangeElement__list PCI_RangeElement__Format_list.
Definition PCI_RangeElement__F1 z :=
  (PCI_RangeElement__pci_RangeIndex z, (PCI_RangeElement__pci_Range z, tt)).
Definition PCI_RangeElement__F2 (y : seq_type PCI_RangeElement__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PCI_RangeElement__Type i0 i1
  end.
Lemma PCI_RangeElement__F1F2_cond (z : PCI_RangeElement__Type)
  : PCI_RangeElement__cond z ->
  (seq_cond PCI_RangeElement__list (PCI_RangeElement__F1 z)).
intro H. unfold PCI_RangeElement__cond in H. simpl. auto. Qed.
Lemma PCI_RangeElement__F1F2_cond2 (z : PCI_RangeElement__Type)
 : PCI_RangeElement__F2 (PCI_RangeElement__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PCI_RangeElement__F2F1_cond (y : seq_type PCI_RangeElement__list)
  : seq_cond PCI_RangeElement__list y ->
 (PCI_RangeElement__cond (PCI_RangeElement__F2 y)) /\  PCI_RangeElement__F1 (PCI_RangeElement__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PCI_RangeElement__cond. simpl in *. auto.
 - simpl. unfold PCI_RangeElement__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PCI_RangeElement__Format : T_Format PCI_RangeElement__Type PCI_RangeElement__cond :=
        proj2_format  PCI_RangeElement__cond PCI_RangeElement__list__Format
    PCI_RangeElement__F1 PCI_RangeElement__F2 PCI_RangeElement__F1F2_cond  PCI_RangeElement__F1F2_cond2 PCI_RangeElement__F2F1_cond.
Opaque PCI_RangeElement__cond PCI_RangeElement__Format.

