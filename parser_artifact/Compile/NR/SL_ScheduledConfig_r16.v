Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.MAC_MainConfigSL_r16.

Opaque MAC_MainConfigSL_r16__cond MAC_MainConfigSL_r16__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Lemma SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__Type := Z.
Definition SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__cond := (fun z => (0 <= z <= 15)%Z).
Definition SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__Type := list Z.

Lemma SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__cond (z : SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__Type) :=  (1 <= Z.of_nat (length z) <= 8)%Z /\ (list_and SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__cond z) .

Require Import NR.SL_ConfiguredGrantConfigList_r16.

Opaque SL_ConfiguredGrantConfigList_r16__cond SL_ConfiguredGrantConfigList_r16__Format.

Lemma SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__Type := Z.
Definition SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__cond := (fun z => (1 <= z <= 32)%Z).
Definition SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__Type := list Z.

Lemma SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__cond (z : SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__Type) :=  (1 <= Z.of_nat (length z) <= 8)%Z /\ (list_and SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__cond z) .

Record SL_ScheduledConfig_r16__ext0O__Type : Set :=
  make__SL_ScheduledConfig_r16__ext0O__Type {
    SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16 : option SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__Type ;
}.
Definition SL_ScheduledConfig_r16__ext0O__list := (
 Opt SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__Type SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__cond ::
 nil).
Definition SL_ScheduledConfig_r16__ext0O__cond z := 
  opt_cond SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__cond (SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16 z) /\
  True.

Definition SL_ScheduledConfig_r16__ext0__Type := SL_ScheduledConfig_r16__ext0O__Type.
Definition SL_ScheduledConfig_r16__ext0__cond := SL_ScheduledConfig_r16__ext0O__cond.

Record SL_ScheduledConfig_r16__Type : Set :=
  make__SL_ScheduledConfig_r16__Type {
    SL_ScheduledConfig_r16__sl_RNTI_r16 : RNTI_Value__Type ;
    SL_ScheduledConfig_r16__mac_MainConfigSL_r16 : option MAC_MainConfigSL_r16__Type ;
    SL_ScheduledConfig_r16__sl_CS_RNTI_r16 : option RNTI_Value__Type ;
    SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16 : option SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__Type ;
    SL_ScheduledConfig_r16__sl_ConfiguredGrantConfigList_r16 : option SL_ConfiguredGrantConfigList_r16__Type ;
    SL_ScheduledConfig_r16__ext0 : option SL_ScheduledConfig_r16__ext0__Type ;
}.
Definition SL_ScheduledConfig_r16__root_list : list seq_elem := (
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Opt MAC_MainConfigSL_r16__Type MAC_MainConfigSL_r16__cond ::
 Opt RNTI_Value__Type RNTI_Value__cond ::
 Opt SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__Type SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__cond ::
 Opt SL_ConfiguredGrantConfigList_r16__Type SL_ConfiguredGrantConfigList_r16__cond ::
 nil).
Definition SL_ScheduledConfig_r16__ext_list : list typ := (
  typ_cons SL_ScheduledConfig_r16__ext0__Type SL_ScheduledConfig_r16__ext0__cond ::
  nil).
Definition SL_ScheduledConfig_r16__cond (z : SL_ScheduledConfig_r16__Type) := 
(  RNTI_Value__cond (SL_ScheduledConfig_r16__sl_RNTI_r16 z) /\
  opt_cond MAC_MainConfigSL_r16__cond (SL_ScheduledConfig_r16__mac_MainConfigSL_r16 z) /\
  opt_cond RNTI_Value__cond (SL_ScheduledConfig_r16__sl_CS_RNTI_r16 z) /\
  opt_cond SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__cond (SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16 z) /\
  opt_cond SL_ConfiguredGrantConfigList_r16__cond (SL_ScheduledConfig_r16__sl_ConfiguredGrantConfigList_r16 z) /\
  True) /\ 
(  opt_cond SL_ScheduledConfig_r16__ext0__cond (SL_ScheduledConfig_r16__ext0 z) /\
  True).


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
Definition SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__Format : T_Format Z SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__cond :=
 ranged_int_format (0) (15) SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__helper1 SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__helper2.

Opaque SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__cond SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__Format.

Definition SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__Format : T_Format SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__Type SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__cond := seq_of_format SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__seq_of__Format 1 8 SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__helper1 SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__helper2.

Opaque SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__cond SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__Format.

Definition SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__Format : T_Format Z SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__cond :=
 ranged_int_format (1) (32) SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__helper1 SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__helper2.

Opaque SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__cond SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__Format.

Definition SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__Format : T_Format SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__Type SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__cond := seq_of_format SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__seq_of__Format 1 8 SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__helper1 SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__helper2.

Opaque SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__cond SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__Format.


Definition SL_ScheduledConfig_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SL_ScheduledConfig_r16__ext0O__list.
Definition SL_ScheduledConfig_r16__ext0O__Format_list : SL_ScheduledConfig_r16__ext0O__Format_Type :=
  (SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16__Format, unit_format).
Definition SL_ScheduledConfig_r16__ext0O__list__Format := (*Eval compute in *) seq_format SL_ScheduledConfig_r16__ext0O__list SL_ScheduledConfig_r16__ext0O__Format_list.
Definition SL_ScheduledConfig_r16__ext0O__F1 z :=
  (SL_ScheduledConfig_r16__ext0O__sl_DCI_ToSL_Trans_r16 z, tt).
Definition SL_ScheduledConfig_r16__ext0O__F2 (y : seq_type SL_ScheduledConfig_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SL_ScheduledConfig_r16__ext0O__Type i0
  end.
Lemma SL_ScheduledConfig_r16__ext0O__F1F2_cond (z : SL_ScheduledConfig_r16__ext0O__Type)
  : SL_ScheduledConfig_r16__ext0O__cond z ->
  (seq_cond SL_ScheduledConfig_r16__ext0O__list (SL_ScheduledConfig_r16__ext0O__F1 z)).
intro H. unfold SL_ScheduledConfig_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SL_ScheduledConfig_r16__ext0O__F1F2_cond2 (z : SL_ScheduledConfig_r16__ext0O__Type)
 : SL_ScheduledConfig_r16__ext0O__F2 (SL_ScheduledConfig_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_ScheduledConfig_r16__ext0O__F2F1_cond (y : seq_type SL_ScheduledConfig_r16__ext0O__list)
  : seq_cond SL_ScheduledConfig_r16__ext0O__list y ->
 (SL_ScheduledConfig_r16__ext0O__cond (SL_ScheduledConfig_r16__ext0O__F2 y)) /\  SL_ScheduledConfig_r16__ext0O__F1 (SL_ScheduledConfig_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_ScheduledConfig_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SL_ScheduledConfig_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_ScheduledConfig_r16__ext0O__Format : T_Format SL_ScheduledConfig_r16__ext0O__Type SL_ScheduledConfig_r16__ext0O__cond :=
        proj2_format  SL_ScheduledConfig_r16__ext0O__cond SL_ScheduledConfig_r16__ext0O__list__Format
    SL_ScheduledConfig_r16__ext0O__F1 SL_ScheduledConfig_r16__ext0O__F2 SL_ScheduledConfig_r16__ext0O__F1F2_cond  SL_ScheduledConfig_r16__ext0O__F1F2_cond2 SL_ScheduledConfig_r16__ext0O__F2F1_cond.
Opaque SL_ScheduledConfig_r16__ext0O__cond SL_ScheduledConfig_r16__ext0O__Format.

Definition SL_ScheduledConfig_r16__ext0__check_all_none (b : SL_ScheduledConfig_r16__ext0O__Type) : bool :=
match b with 
  | make__SL_ScheduledConfig_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SL_ScheduledConfig_r16__ext0__Format : T_Format SL_ScheduledConfig_r16__ext0__Type SL_ScheduledConfig_r16__ext0__cond :=
  restrict_add_format SL_ScheduledConfig_r16__ext0__check_all_none SL_ScheduledConfig_r16__ext0O__Format.

Opaque SL_ScheduledConfig_r16__ext0__cond SL_ScheduledConfig_r16__ext0__Format.


Definition SL_ScheduledConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_ScheduledConfig_r16__root_list.
Definition SL_ScheduledConfig_r16__root_Format_list : SL_ScheduledConfig_r16__root_Format_Type :=
  (RNTI_Value__Format, (MAC_MainConfigSL_r16__Format, (RNTI_Value__Format, (SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16__Format, (SL_ConfiguredGrantConfigList_r16__Format, unit_format))))).

Definition SL_ScheduledConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_ScheduledConfig_r16__ext_list.
Definition SL_ScheduledConfig_r16__ext_Format_list : SL_ScheduledConfig_r16__ext_Format_Type :=
  (SL_ScheduledConfig_r16__ext0__Format, unit__Format).

Definition SL_ScheduledConfig_r16__list_type : Set := (seq_type SL_ScheduledConfig_r16__root_list) * (seq_ext_type SL_ScheduledConfig_r16__ext_list).
Definition SL_ScheduledConfig_r16__list_cond (z : SL_ScheduledConfig_r16__list_type) : Prop :=
        (seq_cond SL_ScheduledConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_ScheduledConfig_r16__ext_list (snd z)).
Definition SL_ScheduledConfig_r16__list_format : T_Format SL_ScheduledConfig_r16__list_type SL_ScheduledConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_ScheduledConfig_r16__root_list SL_ScheduledConfig_r16__root_Format_list SL_ScheduledConfig_r16__ext_list SL_ScheduledConfig_r16__ext_Format_list.

Opaque SL_ScheduledConfig_r16__list_format.
Definition SL_ScheduledConfig_r16__F1 (z : SL_ScheduledConfig_r16__Type) : SL_ScheduledConfig_r16__list_type :=
  (((SL_ScheduledConfig_r16__sl_RNTI_r16 z, (SL_ScheduledConfig_r16__mac_MainConfigSL_r16 z, (SL_ScheduledConfig_r16__sl_CS_RNTI_r16 z, (SL_ScheduledConfig_r16__sl_PSFCH_ToPUCCH_r16 z, (SL_ScheduledConfig_r16__sl_ConfiguredGrantConfigList_r16 z, tt)))))), (
(SL_ScheduledConfig_r16__ext0 z, tt))).
Definition SL_ScheduledConfig_r16__F2 (y : SL_ScheduledConfig_r16__list_type) : SL_ScheduledConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, _))=>
    make__SL_ScheduledConfig_r16__Type j0 j1 j2 j3 j4 i0
  end.
Definition SL_ScheduledConfig_r16__helper1 : (forall a : SL_ScheduledConfig_r16__Type, SL_ScheduledConfig_r16__cond a -> SL_ScheduledConfig_r16__list_cond (SL_ScheduledConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_ScheduledConfig_r16__helper2 : (forall a : SL_ScheduledConfig_r16__Type, SL_ScheduledConfig_r16__F2 (SL_ScheduledConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_ScheduledConfig_r16__helper3 : (forall b : SL_ScheduledConfig_r16__list_type, SL_ScheduledConfig_r16__list_cond b -> SL_ScheduledConfig_r16__cond (SL_ScheduledConfig_r16__F2 b) /\ SL_ScheduledConfig_r16__F1 (SL_ScheduledConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_ScheduledConfig_r16__cond, SL_ScheduledConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_ScheduledConfig_r16__Format : T_Format SL_ScheduledConfig_r16__Type SL_ScheduledConfig_r16__cond :=
 proj2_format SL_ScheduledConfig_r16__cond SL_ScheduledConfig_r16__list_format  SL_ScheduledConfig_r16__F1 SL_ScheduledConfig_r16__F2 SL_ScheduledConfig_r16__helper1 SL_ScheduledConfig_r16__helper2 SL_ScheduledConfig_r16__helper3.

Opaque SL_ScheduledConfig_r16__cond SL_ScheduledConfig_r16__Format.

