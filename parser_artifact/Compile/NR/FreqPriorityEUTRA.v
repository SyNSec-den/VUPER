Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Require Import NR.CellReselectionPriority.

Opaque CellReselectionPriority__cond CellReselectionPriority__Format.

Require Import NR.CellReselectionSubPriority.

Opaque CellReselectionSubPriority__cond CellReselectionSubPriority__Format.

Record FreqPriorityEUTRA__Type : Set :=
  make__FreqPriorityEUTRA__Type {
    FreqPriorityEUTRA__carrierFreq : ARFCN_ValueEUTRA__Type ;
    FreqPriorityEUTRA__cellReselectionPriority : CellReselectionPriority__Type ;
    FreqPriorityEUTRA__cellReselectionSubPriority : option CellReselectionSubPriority__Type ;
}.
Definition FreqPriorityEUTRA__list := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Nor CellReselectionPriority__Type CellReselectionPriority__cond ::
 Opt CellReselectionSubPriority__Type CellReselectionSubPriority__cond ::
 nil).
Definition FreqPriorityEUTRA__cond z := 
  ARFCN_ValueEUTRA__cond (FreqPriorityEUTRA__carrierFreq z) /\
  CellReselectionPriority__cond (FreqPriorityEUTRA__cellReselectionPriority z) /\
  opt_cond CellReselectionSubPriority__cond (FreqPriorityEUTRA__cellReselectionSubPriority z) /\
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

Definition FreqPriorityEUTRA__Format_Type := Eval cbn in seq_format_prod FreqPriorityEUTRA__list.
Definition FreqPriorityEUTRA__Format_list : FreqPriorityEUTRA__Format_Type :=
  (ARFCN_ValueEUTRA__Format, (CellReselectionPriority__Format, (CellReselectionSubPriority__Format, unit_format))).
Definition FreqPriorityEUTRA__list__Format := (*Eval compute in *) seq_format FreqPriorityEUTRA__list FreqPriorityEUTRA__Format_list.
Definition FreqPriorityEUTRA__F1 z :=
  (FreqPriorityEUTRA__carrierFreq z, (FreqPriorityEUTRA__cellReselectionPriority z, (FreqPriorityEUTRA__cellReselectionSubPriority z, tt))).
Definition FreqPriorityEUTRA__F2 (y : seq_type FreqPriorityEUTRA__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FreqPriorityEUTRA__Type i0 i1 i2
  end.
Lemma FreqPriorityEUTRA__F1F2_cond (z : FreqPriorityEUTRA__Type)
  : FreqPriorityEUTRA__cond z ->
  (seq_cond FreqPriorityEUTRA__list (FreqPriorityEUTRA__F1 z)).
intro H. unfold FreqPriorityEUTRA__cond in H. simpl. auto. Qed.
Lemma FreqPriorityEUTRA__F1F2_cond2 (z : FreqPriorityEUTRA__Type)
 : FreqPriorityEUTRA__F2 (FreqPriorityEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FreqPriorityEUTRA__F2F1_cond (y : seq_type FreqPriorityEUTRA__list)
  : seq_cond FreqPriorityEUTRA__list y ->
 (FreqPriorityEUTRA__cond (FreqPriorityEUTRA__F2 y)) /\  FreqPriorityEUTRA__F1 (FreqPriorityEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FreqPriorityEUTRA__cond. simpl in *. auto.
 - simpl. unfold FreqPriorityEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FreqPriorityEUTRA__Format : T_Format FreqPriorityEUTRA__Type FreqPriorityEUTRA__cond :=
        proj2_format  FreqPriorityEUTRA__cond FreqPriorityEUTRA__list__Format
    FreqPriorityEUTRA__F1 FreqPriorityEUTRA__F2 FreqPriorityEUTRA__F1F2_cond  FreqPriorityEUTRA__F1F2_cond2 FreqPriorityEUTRA__F2F1_cond.
Opaque FreqPriorityEUTRA__cond FreqPriorityEUTRA__Format.

