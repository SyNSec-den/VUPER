Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__Type := Z.
Definition SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__cond := (fun z => (1 <= z <= 8)%Z).
Lemma SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__helper1 : (0 <= maxCBR_Level_1_r16)%Z. unfold maxCBR_Level_1_r16.
 lia. Qed.
Lemma SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__helper2 : to_bit_sz (Z.to_nat (maxCBR_Level_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCBR_Level_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__Type := Z.
Definition SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__cond := (fun z => (0 <= z <= maxCBR_Level_1_r16)%Z).
Lemma SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__helper1 : (0 <= maxCBR_Config_1_r16)%Z. unfold maxCBR_Config_1_r16.
 lia. Qed.
Lemma SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__helper2 : to_bit_sz (Z.to_nat (maxCBR_Config_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCBR_Config_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__Type := Z.
Definition SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__cond := (fun z => (0 <= z <= maxCBR_Config_1_r16)%Z).
Require Import NR.SL_TxConfigIndex_r16.

Opaque SL_TxConfigIndex_r16__cond SL_TxConfigIndex_r16__Format.

Definition SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__Type := list SL_TxConfigIndex_r16__Type.

Lemma SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__helper1 : (0 <= 1 <= maxCBR_Level_r16)%Z. unfold maxCBR_Level_r16.
 lia. Qed.
Lemma SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__helper2 : to_bit_sz (Z.to_nat (maxCBR_Level_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCBR_Level_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__cond (z : SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxCBR_Level_r16)%Z /\ (list_and SL_TxConfigIndex_r16__cond z) .

Record SL_PriorityTxConfigIndex_r16__Type : Set :=
  make__SL_PriorityTxConfigIndex_r16__Type {
    SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16 : option Z ;
    SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16 : option Z ;
    SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16 : option Z ;
    SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16 : option SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__Type ;
}.
Definition SL_PriorityTxConfigIndex_r16__list := (
 Opt Z SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__cond ::
 Opt Z SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__cond ::
 Opt Z SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__cond ::
 Opt SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__Type SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__cond ::
 nil).
Definition SL_PriorityTxConfigIndex_r16__cond z := 
  opt_cond SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__cond (SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16 z) /\
  opt_cond SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__cond (SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16 z) /\
  opt_cond SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__cond (SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16 z) /\
  opt_cond SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__cond (SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16 z) /\
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
Definition SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__Format : T_Format Z SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__cond :=
 ranged_int_format (1) (8) SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__helper1 SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__helper2.

Opaque SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__cond SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__Format.

Definition SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__Format : T_Format Z SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__cond :=
 ranged_int_format (0) (maxCBR_Level_1_r16) SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__helper1 SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__helper2.

Opaque SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__cond SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__Format.

Definition SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__Format : T_Format Z SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__cond :=
 ranged_int_format (0) (maxCBR_Config_1_r16) SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__helper1 SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__helper2.

Opaque SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__cond SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__Format.

Definition SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__Format : T_Format SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__Type SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__cond := seq_of_format SL_TxConfigIndex_r16__Format 1 maxCBR_Level_r16 SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__helper1 SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__helper2.

Opaque SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__cond SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__Format.


Definition SL_PriorityTxConfigIndex_r16__Format_Type := Eval cbn in seq_format_prod SL_PriorityTxConfigIndex_r16__list.
Definition SL_PriorityTxConfigIndex_r16__Format_list : SL_PriorityTxConfigIndex_r16__Format_Type :=
  (SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16__Format, (SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16__Format, (SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16__Format, (SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16__Format, unit_format)))).
Definition SL_PriorityTxConfigIndex_r16__list__Format := (*Eval compute in *) seq_format SL_PriorityTxConfigIndex_r16__list SL_PriorityTxConfigIndex_r16__Format_list.
Definition SL_PriorityTxConfigIndex_r16__F1 z :=
  (SL_PriorityTxConfigIndex_r16__sl_PriorityThreshold_r16 z, (SL_PriorityTxConfigIndex_r16__sl_DefaultTxConfigIndex_r16 z, (SL_PriorityTxConfigIndex_r16__sl_CBR_ConfigIndex_r16 z, (SL_PriorityTxConfigIndex_r16__sl_Tx_ConfigIndexList_r16 z, tt)))).
Definition SL_PriorityTxConfigIndex_r16__F2 (y : seq_type SL_PriorityTxConfigIndex_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SL_PriorityTxConfigIndex_r16__Type i0 i1 i2 i3
  end.
Lemma SL_PriorityTxConfigIndex_r16__F1F2_cond (z : SL_PriorityTxConfigIndex_r16__Type)
  : SL_PriorityTxConfigIndex_r16__cond z ->
  (seq_cond SL_PriorityTxConfigIndex_r16__list (SL_PriorityTxConfigIndex_r16__F1 z)).
intro H. unfold SL_PriorityTxConfigIndex_r16__cond in H. simpl. auto. Qed.
Lemma SL_PriorityTxConfigIndex_r16__F1F2_cond2 (z : SL_PriorityTxConfigIndex_r16__Type)
 : SL_PriorityTxConfigIndex_r16__F2 (SL_PriorityTxConfigIndex_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_PriorityTxConfigIndex_r16__F2F1_cond (y : seq_type SL_PriorityTxConfigIndex_r16__list)
  : seq_cond SL_PriorityTxConfigIndex_r16__list y ->
 (SL_PriorityTxConfigIndex_r16__cond (SL_PriorityTxConfigIndex_r16__F2 y)) /\  SL_PriorityTxConfigIndex_r16__F1 (SL_PriorityTxConfigIndex_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_PriorityTxConfigIndex_r16__cond. simpl in *. auto.
 - simpl. unfold SL_PriorityTxConfigIndex_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_PriorityTxConfigIndex_r16__Format : T_Format SL_PriorityTxConfigIndex_r16__Type SL_PriorityTxConfigIndex_r16__cond :=
        proj2_format  SL_PriorityTxConfigIndex_r16__cond SL_PriorityTxConfigIndex_r16__list__Format
    SL_PriorityTxConfigIndex_r16__F1 SL_PriorityTxConfigIndex_r16__F2 SL_PriorityTxConfigIndex_r16__F1F2_cond  SL_PriorityTxConfigIndex_r16__F1F2_cond2 SL_PriorityTxConfigIndex_r16__F2F1_cond.
Opaque SL_PriorityTxConfigIndex_r16__cond SL_PriorityTxConfigIndex_r16__Format.

