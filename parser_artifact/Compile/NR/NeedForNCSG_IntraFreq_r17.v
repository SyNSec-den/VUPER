Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Inductive NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type : Set :=
 | NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__gap
 | NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__ncsg
 | NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nogap_noncsg
.
Definition NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__cond := (fun (_ : NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type) => True).
Lemma NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nat__helper.

Definition NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F1 t :=
  match t with
  | NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__gap => 0
  | NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__ncsg => 1
  | NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nogap_noncsg => 2
  end.
Definition NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F2 n :=
  match n with
  | 0 => NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__gap
  | 1 => NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__ncsg
  | 2 => NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nogap_noncsg
  | _ => NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__gap
  end.
Lemma NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F1F2 : forall x : NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type, (NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F1 x <= 2) /\ NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F2 (NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F1 x) = x. imp_solve. Qed.
Lemma NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F2F1 : forall (y : nat) (H : y <= 2), NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F1 (NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F2 y) = y. enum_solve H y. Qed.

Record NeedForNCSG_IntraFreq_r17__Type : Set :=
  make__NeedForNCSG_IntraFreq_r17__Type {
    NeedForNCSG_IntraFreq_r17__servCellId_r17 : ServCellIndex__Type ;
    NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17 : NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type ;
}.
Definition NeedForNCSG_IntraFreq_r17__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__cond ::
 nil).
Definition NeedForNCSG_IntraFreq_r17__cond z := 
  ServCellIndex__cond (NeedForNCSG_IntraFreq_r17__servCellId_r17 z) /\
  NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__cond (NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17 z) /\
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
Definition NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Format : T_Format NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__nat__Format NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F1 NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F2 NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F1F2 NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__F2F1.

Opaque NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__cond NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Format.


Definition NeedForNCSG_IntraFreq_r17__Format_Type := Eval cbn in seq_format_prod NeedForNCSG_IntraFreq_r17__list.
Definition NeedForNCSG_IntraFreq_r17__Format_list : NeedForNCSG_IntraFreq_r17__Format_Type :=
  (ServCellIndex__Format, (NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17__Format, unit_format)).
Definition NeedForNCSG_IntraFreq_r17__list__Format := (*Eval compute in *) seq_format NeedForNCSG_IntraFreq_r17__list NeedForNCSG_IntraFreq_r17__Format_list.
Definition NeedForNCSG_IntraFreq_r17__F1 z :=
  (NeedForNCSG_IntraFreq_r17__servCellId_r17 z, (NeedForNCSG_IntraFreq_r17__gapIndicationIntra_r17 z, tt)).
Definition NeedForNCSG_IntraFreq_r17__F2 (y : seq_type NeedForNCSG_IntraFreq_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__NeedForNCSG_IntraFreq_r17__Type i0 i1
  end.
Lemma NeedForNCSG_IntraFreq_r17__F1F2_cond (z : NeedForNCSG_IntraFreq_r17__Type)
  : NeedForNCSG_IntraFreq_r17__cond z ->
  (seq_cond NeedForNCSG_IntraFreq_r17__list (NeedForNCSG_IntraFreq_r17__F1 z)).
intro H. unfold NeedForNCSG_IntraFreq_r17__cond in H. simpl. auto. Qed.
Lemma NeedForNCSG_IntraFreq_r17__F1F2_cond2 (z : NeedForNCSG_IntraFreq_r17__Type)
 : NeedForNCSG_IntraFreq_r17__F2 (NeedForNCSG_IntraFreq_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NeedForNCSG_IntraFreq_r17__F2F1_cond (y : seq_type NeedForNCSG_IntraFreq_r17__list)
  : seq_cond NeedForNCSG_IntraFreq_r17__list y ->
 (NeedForNCSG_IntraFreq_r17__cond (NeedForNCSG_IntraFreq_r17__F2 y)) /\  NeedForNCSG_IntraFreq_r17__F1 (NeedForNCSG_IntraFreq_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NeedForNCSG_IntraFreq_r17__cond. simpl in *. auto.
 - simpl. unfold NeedForNCSG_IntraFreq_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NeedForNCSG_IntraFreq_r17__Format : T_Format NeedForNCSG_IntraFreq_r17__Type NeedForNCSG_IntraFreq_r17__cond :=
        proj2_format  NeedForNCSG_IntraFreq_r17__cond NeedForNCSG_IntraFreq_r17__list__Format
    NeedForNCSG_IntraFreq_r17__F1 NeedForNCSG_IntraFreq_r17__F2 NeedForNCSG_IntraFreq_r17__F1F2_cond  NeedForNCSG_IntraFreq_r17__F1F2_cond2 NeedForNCSG_IntraFreq_r17__F2F1_cond.
Opaque NeedForNCSG_IntraFreq_r17__cond NeedForNCSG_IntraFreq_r17__Format.

