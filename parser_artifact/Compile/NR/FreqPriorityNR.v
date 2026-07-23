Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.CellReselectionPriority.

Opaque CellReselectionPriority__cond CellReselectionPriority__Format.

Require Import NR.CellReselectionSubPriority.

Opaque CellReselectionSubPriority__cond CellReselectionSubPriority__Format.

Record FreqPriorityNR__Type : Set :=
  make__FreqPriorityNR__Type {
    FreqPriorityNR__carrierFreq : ARFCN_ValueNR__Type ;
    FreqPriorityNR__cellReselectionPriority : CellReselectionPriority__Type ;
    FreqPriorityNR__cellReselectionSubPriority : option CellReselectionSubPriority__Type ;
}.
Definition FreqPriorityNR__list := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor CellReselectionPriority__Type CellReselectionPriority__cond ::
 Opt CellReselectionSubPriority__Type CellReselectionSubPriority__cond ::
 nil).
Definition FreqPriorityNR__cond z := 
  ARFCN_ValueNR__cond (FreqPriorityNR__carrierFreq z) /\
  CellReselectionPriority__cond (FreqPriorityNR__cellReselectionPriority z) /\
  opt_cond CellReselectionSubPriority__cond (FreqPriorityNR__cellReselectionSubPriority z) /\
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

Definition FreqPriorityNR__Format_Type := Eval cbn in seq_format_prod FreqPriorityNR__list.
Definition FreqPriorityNR__Format_list : FreqPriorityNR__Format_Type :=
  (ARFCN_ValueNR__Format, (CellReselectionPriority__Format, (CellReselectionSubPriority__Format, unit_format))).
Definition FreqPriorityNR__list__Format := (*Eval compute in *) seq_format FreqPriorityNR__list FreqPriorityNR__Format_list.
Definition FreqPriorityNR__F1 z :=
  (FreqPriorityNR__carrierFreq z, (FreqPriorityNR__cellReselectionPriority z, (FreqPriorityNR__cellReselectionSubPriority z, tt))).
Definition FreqPriorityNR__F2 (y : seq_type FreqPriorityNR__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FreqPriorityNR__Type i0 i1 i2
  end.
Lemma FreqPriorityNR__F1F2_cond (z : FreqPriorityNR__Type)
  : FreqPriorityNR__cond z ->
  (seq_cond FreqPriorityNR__list (FreqPriorityNR__F1 z)).
intro H. unfold FreqPriorityNR__cond in H. simpl. auto. Qed.
Lemma FreqPriorityNR__F1F2_cond2 (z : FreqPriorityNR__Type)
 : FreqPriorityNR__F2 (FreqPriorityNR__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FreqPriorityNR__F2F1_cond (y : seq_type FreqPriorityNR__list)
  : seq_cond FreqPriorityNR__list y ->
 (FreqPriorityNR__cond (FreqPriorityNR__F2 y)) /\  FreqPriorityNR__F1 (FreqPriorityNR__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FreqPriorityNR__cond. simpl in *. auto.
 - simpl. unfold FreqPriorityNR__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FreqPriorityNR__Format : T_Format FreqPriorityNR__Type FreqPriorityNR__cond :=
        proj2_format  FreqPriorityNR__cond FreqPriorityNR__list__Format
    FreqPriorityNR__F1 FreqPriorityNR__F2 FreqPriorityNR__F1F2_cond  FreqPriorityNR__F1F2_cond2 FreqPriorityNR__F2F1_cond.
Opaque FreqPriorityNR__cond FreqPriorityNR__Format.

