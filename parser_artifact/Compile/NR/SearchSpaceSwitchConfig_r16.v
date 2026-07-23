Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CellGroupForSwitch_r16.

Opaque CellGroupForSwitch_r16__cond CellGroupForSwitch_r16__Format.

Definition SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__Type := list CellGroupForSwitch_r16__Type.

Lemma SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__cond (z : SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and CellGroupForSwitch_r16__cond z) .

Lemma SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__helper1 : (10 <= 52)%Z.  lia. Qed.
Lemma SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__helper2 : to_bit_sz (Z.to_nat (52 - 10)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (52 - 10))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__Type := Z.
Definition SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__cond := (fun z => (10 <= z <= 52)%Z).
Record SearchSpaceSwitchConfig_r16__Type : Set :=
  make__SearchSpaceSwitchConfig_r16__Type {
    SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16 : option SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__Type ;
    SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16 : option Z ;
}.
Definition SearchSpaceSwitchConfig_r16__list := (
 Opt SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__Type SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__cond ::
 Opt Z SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__cond ::
 nil).
Definition SearchSpaceSwitchConfig_r16__cond z := 
  opt_cond SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__cond (SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16 z) /\
  opt_cond SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__cond (SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16 z) /\
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
Definition SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__Format : T_Format SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__Type SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__cond := seq_of_format CellGroupForSwitch_r16__Format 1 4 SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__helper1 SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__helper2.

Opaque SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__cond SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__Format.

Definition SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__Format : T_Format Z SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__cond :=
 ranged_int_format (10) (52) SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__helper1 SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__helper2.

Opaque SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__cond SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__Format.


Definition SearchSpaceSwitchConfig_r16__Format_Type := Eval cbn in seq_format_prod SearchSpaceSwitchConfig_r16__list.
Definition SearchSpaceSwitchConfig_r16__Format_list : SearchSpaceSwitchConfig_r16__Format_Type :=
  (SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16__Format, (SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16__Format, unit_format)).
Definition SearchSpaceSwitchConfig_r16__list__Format := (*Eval compute in *) seq_format SearchSpaceSwitchConfig_r16__list SearchSpaceSwitchConfig_r16__Format_list.
Definition SearchSpaceSwitchConfig_r16__F1 z :=
  (SearchSpaceSwitchConfig_r16__cellGroupsForSwitchList_r16 z, (SearchSpaceSwitchConfig_r16__searchSpaceSwitchDelay_r16 z, tt)).
Definition SearchSpaceSwitchConfig_r16__F2 (y : seq_type SearchSpaceSwitchConfig_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SearchSpaceSwitchConfig_r16__Type i0 i1
  end.
Lemma SearchSpaceSwitchConfig_r16__F1F2_cond (z : SearchSpaceSwitchConfig_r16__Type)
  : SearchSpaceSwitchConfig_r16__cond z ->
  (seq_cond SearchSpaceSwitchConfig_r16__list (SearchSpaceSwitchConfig_r16__F1 z)).
intro H. unfold SearchSpaceSwitchConfig_r16__cond in H. simpl. auto. Qed.
Lemma SearchSpaceSwitchConfig_r16__F1F2_cond2 (z : SearchSpaceSwitchConfig_r16__Type)
 : SearchSpaceSwitchConfig_r16__F2 (SearchSpaceSwitchConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpaceSwitchConfig_r16__F2F1_cond (y : seq_type SearchSpaceSwitchConfig_r16__list)
  : seq_cond SearchSpaceSwitchConfig_r16__list y ->
 (SearchSpaceSwitchConfig_r16__cond (SearchSpaceSwitchConfig_r16__F2 y)) /\  SearchSpaceSwitchConfig_r16__F1 (SearchSpaceSwitchConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpaceSwitchConfig_r16__cond. simpl in *. auto.
 - simpl. unfold SearchSpaceSwitchConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpaceSwitchConfig_r16__Format : T_Format SearchSpaceSwitchConfig_r16__Type SearchSpaceSwitchConfig_r16__cond :=
        proj2_format  SearchSpaceSwitchConfig_r16__cond SearchSpaceSwitchConfig_r16__list__Format
    SearchSpaceSwitchConfig_r16__F1 SearchSpaceSwitchConfig_r16__F2 SearchSpaceSwitchConfig_r16__F1F2_cond  SearchSpaceSwitchConfig_r16__F1F2_cond2 SearchSpaceSwitchConfig_r16__F2F1_cond.
Opaque SearchSpaceSwitchConfig_r16__cond SearchSpaceSwitchConfig_r16__Format.

