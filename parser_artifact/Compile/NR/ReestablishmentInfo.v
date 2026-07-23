Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.ShortMAC_I.

Opaque ShortMAC_I__cond ShortMAC_I__Format.

Require Import NR.ReestabNCellInfoList.

Opaque ReestabNCellInfoList__cond ReestabNCellInfoList__Format.

Record ReestablishmentInfo__Type : Set :=
  make__ReestablishmentInfo__Type {
    ReestablishmentInfo__sourcePhysCellId : PhysCellId__Type ;
    ReestablishmentInfo__targetCellShortMAC_I : ShortMAC_I__Type ;
    ReestablishmentInfo__additionalReestabInfoList : option ReestabNCellInfoList__Type ;
}.
Definition ReestablishmentInfo__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor ShortMAC_I__Type ShortMAC_I__cond ::
 Opt ReestabNCellInfoList__Type ReestabNCellInfoList__cond ::
 nil).
Definition ReestablishmentInfo__cond z := 
  PhysCellId__cond (ReestablishmentInfo__sourcePhysCellId z) /\
  ShortMAC_I__cond (ReestablishmentInfo__targetCellShortMAC_I z) /\
  opt_cond ReestabNCellInfoList__cond (ReestablishmentInfo__additionalReestabInfoList z) /\
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

Definition ReestablishmentInfo__Format_Type := Eval cbn in seq_format_prod ReestablishmentInfo__list.
Definition ReestablishmentInfo__Format_list : ReestablishmentInfo__Format_Type :=
  (PhysCellId__Format, (ShortMAC_I__Format, (ReestabNCellInfoList__Format, unit_format))).
Definition ReestablishmentInfo__list__Format := (*Eval compute in *) seq_format ReestablishmentInfo__list ReestablishmentInfo__Format_list.
Definition ReestablishmentInfo__F1 z :=
  (ReestablishmentInfo__sourcePhysCellId z, (ReestablishmentInfo__targetCellShortMAC_I z, (ReestablishmentInfo__additionalReestabInfoList z, tt))).
Definition ReestablishmentInfo__F2 (y : seq_type ReestablishmentInfo__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ReestablishmentInfo__Type i0 i1 i2
  end.
Lemma ReestablishmentInfo__F1F2_cond (z : ReestablishmentInfo__Type)
  : ReestablishmentInfo__cond z ->
  (seq_cond ReestablishmentInfo__list (ReestablishmentInfo__F1 z)).
intro H. unfold ReestablishmentInfo__cond in H. simpl. auto. Qed.
Lemma ReestablishmentInfo__F1F2_cond2 (z : ReestablishmentInfo__Type)
 : ReestablishmentInfo__F2 (ReestablishmentInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReestablishmentInfo__F2F1_cond (y : seq_type ReestablishmentInfo__list)
  : seq_cond ReestablishmentInfo__list y ->
 (ReestablishmentInfo__cond (ReestablishmentInfo__F2 y)) /\  ReestablishmentInfo__F1 (ReestablishmentInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReestablishmentInfo__cond. simpl in *. auto.
 - simpl. unfold ReestablishmentInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReestablishmentInfo__Format : T_Format ReestablishmentInfo__Type ReestablishmentInfo__cond :=
        proj2_format  ReestablishmentInfo__cond ReestablishmentInfo__list__Format
    ReestablishmentInfo__F1 ReestablishmentInfo__F2 ReestablishmentInfo__F1F2_cond  ReestablishmentInfo__F1F2_cond2 ReestablishmentInfo__F2F1_cond.
Opaque ReestablishmentInfo__cond ReestablishmentInfo__Format.

