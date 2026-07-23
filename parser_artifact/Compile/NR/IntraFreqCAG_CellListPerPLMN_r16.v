Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__helper1 : (1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__Type := Z.
Definition IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__cond := (fun z => (1 <= z <= maxPLMN)%Z).
Require Import NR.PCI_Range.

Opaque PCI_Range__cond PCI_Range__Format.

Definition IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__Type := list PCI_Range__Type.

Lemma IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__helper1 : (0 <= 1 <= maxCAG_Cell_r16)%Z. unfold maxCAG_Cell_r16.
 lia. Qed.
Lemma IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__helper2 : to_bit_sz (Z.to_nat (maxCAG_Cell_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCAG_Cell_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__cond (z : IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxCAG_Cell_r16)%Z /\ (list_and PCI_Range__cond z) .

Record IntraFreqCAG_CellListPerPLMN_r16__Type : Set :=
  make__IntraFreqCAG_CellListPerPLMN_r16__Type {
    IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16 : Z ;
    IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16 : IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__Type ;
}.
Definition IntraFreqCAG_CellListPerPLMN_r16__list := (
 Nor Z IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__cond ::
 Nor IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__Type IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__cond ::
 nil).
Definition IntraFreqCAG_CellListPerPLMN_r16__cond z := 
  IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__cond (IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16 z) /\
  IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__cond (IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16 z) /\
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
Definition IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__Format : T_Format Z IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__cond :=
 ranged_int_format (1) (maxPLMN) IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__helper1 IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__helper2.

Opaque IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__cond IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__Format.

Definition IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__Format : T_Format IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__Type IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__cond := seq_of_format PCI_Range__Format 1 maxCAG_Cell_r16 IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__helper1 IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__helper2.

Opaque IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__cond IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__Format.


Definition IntraFreqCAG_CellListPerPLMN_r16__Format_Type := Eval cbn in seq_format_prod IntraFreqCAG_CellListPerPLMN_r16__list.
Definition IntraFreqCAG_CellListPerPLMN_r16__Format_list : IntraFreqCAG_CellListPerPLMN_r16__Format_Type :=
  (IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16__Format, (IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16__Format, unit_format)).
Definition IntraFreqCAG_CellListPerPLMN_r16__list__Format := (*Eval compute in *) seq_format IntraFreqCAG_CellListPerPLMN_r16__list IntraFreqCAG_CellListPerPLMN_r16__Format_list.
Definition IntraFreqCAG_CellListPerPLMN_r16__F1 z :=
  (IntraFreqCAG_CellListPerPLMN_r16__plmn_IdentityIndex_r16 z, (IntraFreqCAG_CellListPerPLMN_r16__cag_CellList_r16 z, tt)).
Definition IntraFreqCAG_CellListPerPLMN_r16__F2 (y : seq_type IntraFreqCAG_CellListPerPLMN_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__IntraFreqCAG_CellListPerPLMN_r16__Type i0 i1
  end.
Lemma IntraFreqCAG_CellListPerPLMN_r16__F1F2_cond (z : IntraFreqCAG_CellListPerPLMN_r16__Type)
  : IntraFreqCAG_CellListPerPLMN_r16__cond z ->
  (seq_cond IntraFreqCAG_CellListPerPLMN_r16__list (IntraFreqCAG_CellListPerPLMN_r16__F1 z)).
intro H. unfold IntraFreqCAG_CellListPerPLMN_r16__cond in H. simpl. auto. Qed.
Lemma IntraFreqCAG_CellListPerPLMN_r16__F1F2_cond2 (z : IntraFreqCAG_CellListPerPLMN_r16__Type)
 : IntraFreqCAG_CellListPerPLMN_r16__F2 (IntraFreqCAG_CellListPerPLMN_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma IntraFreqCAG_CellListPerPLMN_r16__F2F1_cond (y : seq_type IntraFreqCAG_CellListPerPLMN_r16__list)
  : seq_cond IntraFreqCAG_CellListPerPLMN_r16__list y ->
 (IntraFreqCAG_CellListPerPLMN_r16__cond (IntraFreqCAG_CellListPerPLMN_r16__F2 y)) /\  IntraFreqCAG_CellListPerPLMN_r16__F1 (IntraFreqCAG_CellListPerPLMN_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold IntraFreqCAG_CellListPerPLMN_r16__cond. simpl in *. auto.
 - simpl. unfold IntraFreqCAG_CellListPerPLMN_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition IntraFreqCAG_CellListPerPLMN_r16__Format : T_Format IntraFreqCAG_CellListPerPLMN_r16__Type IntraFreqCAG_CellListPerPLMN_r16__cond :=
        proj2_format  IntraFreqCAG_CellListPerPLMN_r16__cond IntraFreqCAG_CellListPerPLMN_r16__list__Format
    IntraFreqCAG_CellListPerPLMN_r16__F1 IntraFreqCAG_CellListPerPLMN_r16__F2 IntraFreqCAG_CellListPerPLMN_r16__F1F2_cond  IntraFreqCAG_CellListPerPLMN_r16__F1F2_cond2 IntraFreqCAG_CellListPerPLMN_r16__F2F1_cond.
Opaque IntraFreqCAG_CellListPerPLMN_r16__cond IntraFreqCAG_CellListPerPLMN_r16__Format.

