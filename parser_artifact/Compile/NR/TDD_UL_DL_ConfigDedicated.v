Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TDD_UL_DL_SlotConfig.

Opaque TDD_UL_DL_SlotConfig__cond TDD_UL_DL_SlotConfig__Format.

Definition TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__Type := list TDD_UL_DL_SlotConfig__Type.

Lemma TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__helper1 : (0 <= 1 <= maxNrofSlots)%Z. unfold maxNrofSlots.
 lia. Qed.
Lemma TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofSlots - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSlots - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__cond (z : TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSlots)%Z /\ (list_and TDD_UL_DL_SlotConfig__cond z) .

Require Import NR.TDD_UL_DL_SlotIndex.

Opaque TDD_UL_DL_SlotIndex__cond TDD_UL_DL_SlotIndex__Format.

Definition TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__Type := list TDD_UL_DL_SlotIndex__Type.

Lemma TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__helper1 : (0 <= 1 <= maxNrofSlots)%Z. unfold maxNrofSlots.
 lia. Qed.
Lemma TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofSlots - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSlots - 1))%Z). { apply Zorder.Zle_minus_le_0. apply TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__cond (z : TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSlots)%Z /\ (list_and TDD_UL_DL_SlotIndex__cond z) .

Record TDD_UL_DL_ConfigDedicated__Type : Set :=
  make__TDD_UL_DL_ConfigDedicated__Type {
    TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList : option TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__Type ;
    TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList : option TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__Type ;
}.
Definition TDD_UL_DL_ConfigDedicated__root_list : list seq_elem := (
 Opt TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__Type TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__cond ::
 Opt TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__Type TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__cond ::
 nil).
Definition TDD_UL_DL_ConfigDedicated__ext_list : list typ := (
  nil).
Definition TDD_UL_DL_ConfigDedicated__cond (z : TDD_UL_DL_ConfigDedicated__Type) := 
(  opt_cond TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__cond (TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList z) /\
  opt_cond TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__cond (TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList z) /\
  True) /\ 
(  True).


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
Definition TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__Format : T_Format TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__Type TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__cond := seq_of_format TDD_UL_DL_SlotConfig__Format 1 maxNrofSlots TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__helper1 TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__helper2.

Opaque TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__cond TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__Format.

Definition TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__Format : T_Format TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__Type TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__cond := seq_of_format TDD_UL_DL_SlotIndex__Format 1 maxNrofSlots TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__helper1 TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__helper2.

Opaque TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__cond TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__Format.


Definition TDD_UL_DL_ConfigDedicated__root_Format_Type := Eval cbn in seq_format_prod TDD_UL_DL_ConfigDedicated__root_list.
Definition TDD_UL_DL_ConfigDedicated__root_Format_list : TDD_UL_DL_ConfigDedicated__root_Format_Type :=
  (TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList__Format, (TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList__Format, unit_format)).

Definition TDD_UL_DL_ConfigDedicated__ext_Format_Type := Eval cbn in get_formats TDD_UL_DL_ConfigDedicated__ext_list.
Definition TDD_UL_DL_ConfigDedicated__ext_Format_list : TDD_UL_DL_ConfigDedicated__ext_Format_Type :=
  unit__Format.

Definition TDD_UL_DL_ConfigDedicated__list_type : Set := (seq_type TDD_UL_DL_ConfigDedicated__root_list) * (seq_ext_type TDD_UL_DL_ConfigDedicated__ext_list).
Definition TDD_UL_DL_ConfigDedicated__list_cond (z : TDD_UL_DL_ConfigDedicated__list_type) : Prop :=
        (seq_cond TDD_UL_DL_ConfigDedicated__root_list (fst z)) /\ (seq_ext_cond TDD_UL_DL_ConfigDedicated__ext_list (snd z)).
Definition TDD_UL_DL_ConfigDedicated__list_format : T_Format TDD_UL_DL_ConfigDedicated__list_type TDD_UL_DL_ConfigDedicated__list_cond :=
 (* Eval compute in *) seq_ext_format TDD_UL_DL_ConfigDedicated__root_list TDD_UL_DL_ConfigDedicated__root_Format_list TDD_UL_DL_ConfigDedicated__ext_list TDD_UL_DL_ConfigDedicated__ext_Format_list.

Opaque TDD_UL_DL_ConfigDedicated__list_format.
Definition TDD_UL_DL_ConfigDedicated__F1 (z : TDD_UL_DL_ConfigDedicated__Type) : TDD_UL_DL_ConfigDedicated__list_type :=
  (((TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToAddModList z, (TDD_UL_DL_ConfigDedicated__slotSpecificConfigurationsToReleaseList z, tt))), (
tt)).
Definition TDD_UL_DL_ConfigDedicated__F2 (y : TDD_UL_DL_ConfigDedicated__list_type) : TDD_UL_DL_ConfigDedicated__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__TDD_UL_DL_ConfigDedicated__Type j0 j1
  end.
Definition TDD_UL_DL_ConfigDedicated__helper1 : (forall a : TDD_UL_DL_ConfigDedicated__Type, TDD_UL_DL_ConfigDedicated__cond a -> TDD_UL_DL_ConfigDedicated__list_cond (TDD_UL_DL_ConfigDedicated__F1 a)).
                     intros. destruct a. auto. Qed.
Definition TDD_UL_DL_ConfigDedicated__helper2 : (forall a : TDD_UL_DL_ConfigDedicated__Type, TDD_UL_DL_ConfigDedicated__F2 (TDD_UL_DL_ConfigDedicated__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition TDD_UL_DL_ConfigDedicated__helper3 : (forall b : TDD_UL_DL_ConfigDedicated__list_type, TDD_UL_DL_ConfigDedicated__list_cond b -> TDD_UL_DL_ConfigDedicated__cond (TDD_UL_DL_ConfigDedicated__F2 b) /\ TDD_UL_DL_ConfigDedicated__F1 (TDD_UL_DL_ConfigDedicated__F2 b) = b).
                     intros. destruct b as [y y1]. unfold TDD_UL_DL_ConfigDedicated__cond, TDD_UL_DL_ConfigDedicated__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition TDD_UL_DL_ConfigDedicated__Format : T_Format TDD_UL_DL_ConfigDedicated__Type TDD_UL_DL_ConfigDedicated__cond :=
 proj2_format TDD_UL_DL_ConfigDedicated__cond TDD_UL_DL_ConfigDedicated__list_format  TDD_UL_DL_ConfigDedicated__F1 TDD_UL_DL_ConfigDedicated__F2 TDD_UL_DL_ConfigDedicated__helper1 TDD_UL_DL_ConfigDedicated__helper2 TDD_UL_DL_ConfigDedicated__helper3.

Opaque TDD_UL_DL_ConfigDedicated__cond TDD_UL_DL_ConfigDedicated__Format.

