Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.VarConnEstFailReport_r16.

Opaque VarConnEstFailReport_r16__cond VarConnEstFailReport_r16__Format.

Definition VarConnEstFailReportList_r17__connEstFailReportList_r17__Type := list VarConnEstFailReport_r16__Type.

Lemma VarConnEstFailReportList_r17__connEstFailReportList_r17__helper1 : (0 <= 1 <= maxCEFReport_r17)%Z. unfold maxCEFReport_r17.
 lia. Qed.
Lemma VarConnEstFailReportList_r17__connEstFailReportList_r17__helper2 : to_bit_sz (Z.to_nat (maxCEFReport_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCEFReport_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply VarConnEstFailReportList_r17__connEstFailReportList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition VarConnEstFailReportList_r17__connEstFailReportList_r17__cond (z : VarConnEstFailReportList_r17__connEstFailReportList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxCEFReport_r17)%Z /\ (list_and VarConnEstFailReport_r16__cond z) .

Record VarConnEstFailReportList_r17__Type : Set :=
  make__VarConnEstFailReportList_r17__Type {
    VarConnEstFailReportList_r17__connEstFailReportList_r17 : VarConnEstFailReportList_r17__connEstFailReportList_r17__Type ;
}.
Definition VarConnEstFailReportList_r17__list := (
 Nor VarConnEstFailReportList_r17__connEstFailReportList_r17__Type VarConnEstFailReportList_r17__connEstFailReportList_r17__cond ::
 nil).
Definition VarConnEstFailReportList_r17__cond z := 
  VarConnEstFailReportList_r17__connEstFailReportList_r17__cond (VarConnEstFailReportList_r17__connEstFailReportList_r17 z) /\
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
Definition VarConnEstFailReportList_r17__connEstFailReportList_r17__Format : T_Format VarConnEstFailReportList_r17__connEstFailReportList_r17__Type VarConnEstFailReportList_r17__connEstFailReportList_r17__cond := seq_of_format VarConnEstFailReport_r16__Format 1 maxCEFReport_r17 VarConnEstFailReportList_r17__connEstFailReportList_r17__helper1 VarConnEstFailReportList_r17__connEstFailReportList_r17__helper2.

Opaque VarConnEstFailReportList_r17__connEstFailReportList_r17__cond VarConnEstFailReportList_r17__connEstFailReportList_r17__Format.


Definition VarConnEstFailReportList_r17__Format_Type := Eval cbn in seq_format_prod VarConnEstFailReportList_r17__list.
Definition VarConnEstFailReportList_r17__Format_list : VarConnEstFailReportList_r17__Format_Type :=
  (VarConnEstFailReportList_r17__connEstFailReportList_r17__Format, unit_format).
Definition VarConnEstFailReportList_r17__list__Format := (*Eval compute in *) seq_format VarConnEstFailReportList_r17__list VarConnEstFailReportList_r17__Format_list.
Definition VarConnEstFailReportList_r17__F1 z :=
  (VarConnEstFailReportList_r17__connEstFailReportList_r17 z, tt).
Definition VarConnEstFailReportList_r17__F2 (y : seq_type VarConnEstFailReportList_r17__list) :=
  match y with
  | (i0, _)=>
    make__VarConnEstFailReportList_r17__Type i0
  end.
Lemma VarConnEstFailReportList_r17__F1F2_cond (z : VarConnEstFailReportList_r17__Type)
  : VarConnEstFailReportList_r17__cond z ->
  (seq_cond VarConnEstFailReportList_r17__list (VarConnEstFailReportList_r17__F1 z)).
intro H. unfold VarConnEstFailReportList_r17__cond in H. simpl. auto. Qed.
Lemma VarConnEstFailReportList_r17__F1F2_cond2 (z : VarConnEstFailReportList_r17__Type)
 : VarConnEstFailReportList_r17__F2 (VarConnEstFailReportList_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarConnEstFailReportList_r17__F2F1_cond (y : seq_type VarConnEstFailReportList_r17__list)
  : seq_cond VarConnEstFailReportList_r17__list y ->
 (VarConnEstFailReportList_r17__cond (VarConnEstFailReportList_r17__F2 y)) /\  VarConnEstFailReportList_r17__F1 (VarConnEstFailReportList_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarConnEstFailReportList_r17__cond. simpl in *. auto.
 - simpl. unfold VarConnEstFailReportList_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarConnEstFailReportList_r17__Format : T_Format VarConnEstFailReportList_r17__Type VarConnEstFailReportList_r17__cond :=
        proj2_format  VarConnEstFailReportList_r17__cond VarConnEstFailReportList_r17__list__Format
    VarConnEstFailReportList_r17__F1 VarConnEstFailReportList_r17__F2 VarConnEstFailReportList_r17__F1F2_cond  VarConnEstFailReportList_r17__F1F2_cond2 VarConnEstFailReportList_r17__F2F1_cond.
Opaque VarConnEstFailReportList_r17__cond VarConnEstFailReportList_r17__Format.

