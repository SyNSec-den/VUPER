Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SlotFormatIndicator.
Definition PDCCH_ServingCellConfig__slotFormatIndicator__Type := SetupRelease__Type SlotFormatIndicator__Type.
Definition PDCCH_ServingCellConfig__slotFormatIndicator__cond := SetupRelease__cond _ SlotFormatIndicator__cond.
Definition PDCCH_ServingCellConfig__slotFormatIndicator__Format : T_Format PDCCH_ServingCellConfig__slotFormatIndicator__Type PDCCH_ServingCellConfig__slotFormatIndicator__cond := SetupRelease__Format _ _ SlotFormatIndicator__Format.
Opaque PDCCH_ServingCellConfig__slotFormatIndicator__cond PDCCH_ServingCellConfig__slotFormatIndicator__Format.

Require Import NR.SetupRelease.
Require Import NR.AvailabilityIndicator_r16.
Definition PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__Type := SetupRelease__Type AvailabilityIndicator_r16__Type.
Definition PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__cond := SetupRelease__cond _ AvailabilityIndicator_r16__cond.
Definition PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__Format : T_Format PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__Type PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__cond := SetupRelease__Format _ _ AvailabilityIndicator_r16__Format.
Opaque PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__cond PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__Format.

Lemma PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__helper1 : (1 <= 80)%Z.  lia. Qed.
Lemma PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__helper2 : to_bit_sz (Z.to_nat (80 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (80 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__Type := Z.
Definition PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__cond := (fun z => (1 <= z <= 80)%Z).
Record PDCCH_ServingCellConfig__ext0O__Type : Set :=
  make__PDCCH_ServingCellConfig__ext0O__Type {
    PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16 : option PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__Type ;
    PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16 : option Z ;
}.
Definition PDCCH_ServingCellConfig__ext0O__list := (
 Opt PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__Type PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__cond ::
 Opt Z PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__cond ::
 nil).
Definition PDCCH_ServingCellConfig__ext0O__cond z := 
  opt_cond PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__cond (PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16 z) /\
  opt_cond PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__cond (PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16 z) /\
  True.

Definition PDCCH_ServingCellConfig__ext0__Type := PDCCH_ServingCellConfig__ext0O__Type.
Definition PDCCH_ServingCellConfig__ext0__cond := PDCCH_ServingCellConfig__ext0O__cond.

Lemma PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__helper1 : (81 <= 1280)%Z.  lia. Qed.
Lemma PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__helper2 : to_bit_sz (Z.to_nat (1280 - 81)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1280 - 81))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__Type := Z.
Definition PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__cond := (fun z => (81 <= z <= 1280)%Z).
Record PDCCH_ServingCellConfig__ext1O__Type : Set :=
  make__PDCCH_ServingCellConfig__ext1O__Type {
    PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710 : option Z ;
}.
Definition PDCCH_ServingCellConfig__ext1O__list := (
 Opt Z PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__cond ::
 nil).
Definition PDCCH_ServingCellConfig__ext1O__cond z := 
  opt_cond PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__cond (PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710 z) /\
  True.

Definition PDCCH_ServingCellConfig__ext1__Type := PDCCH_ServingCellConfig__ext1O__Type.
Definition PDCCH_ServingCellConfig__ext1__cond := PDCCH_ServingCellConfig__ext1O__cond.

Record PDCCH_ServingCellConfig__Type : Set :=
  make__PDCCH_ServingCellConfig__Type {
    PDCCH_ServingCellConfig__slotFormatIndicator : option PDCCH_ServingCellConfig__slotFormatIndicator__Type ;
    PDCCH_ServingCellConfig__ext0 : option PDCCH_ServingCellConfig__ext0__Type ;
    PDCCH_ServingCellConfig__ext1 : option PDCCH_ServingCellConfig__ext1__Type ;
}.
Definition PDCCH_ServingCellConfig__root_list : list seq_elem := (
 Opt PDCCH_ServingCellConfig__slotFormatIndicator__Type PDCCH_ServingCellConfig__slotFormatIndicator__cond ::
 nil).
Definition PDCCH_ServingCellConfig__ext_list : list typ := (
  typ_cons PDCCH_ServingCellConfig__ext0__Type PDCCH_ServingCellConfig__ext0__cond ::
  typ_cons PDCCH_ServingCellConfig__ext1__Type PDCCH_ServingCellConfig__ext1__cond ::
  nil).
Definition PDCCH_ServingCellConfig__cond (z : PDCCH_ServingCellConfig__Type) := 
(  opt_cond PDCCH_ServingCellConfig__slotFormatIndicator__cond (PDCCH_ServingCellConfig__slotFormatIndicator z) /\
  True) /\ 
(  opt_cond PDCCH_ServingCellConfig__ext0__cond (PDCCH_ServingCellConfig__ext0 z) /\
  opt_cond PDCCH_ServingCellConfig__ext1__cond (PDCCH_ServingCellConfig__ext1 z) /\
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
Opaque PDCCH_ServingCellConfig__slotFormatIndicator__cond PDCCH_ServingCellConfig__slotFormatIndicator__Format.

Opaque PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__cond PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__Format.

Definition PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__Format : T_Format Z PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__cond :=
 ranged_int_format (1) (80) PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__helper1 PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__helper2.

Opaque PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__cond PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__Format.


Definition PDCCH_ServingCellConfig__ext0O__Format_Type := Eval cbn in seq_format_prod PDCCH_ServingCellConfig__ext0O__list.
Definition PDCCH_ServingCellConfig__ext0O__Format_list : PDCCH_ServingCellConfig__ext0O__Format_Type :=
  (PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16__Format, (PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16__Format, unit_format)).
Definition PDCCH_ServingCellConfig__ext0O__list__Format := (*Eval compute in *) seq_format PDCCH_ServingCellConfig__ext0O__list PDCCH_ServingCellConfig__ext0O__Format_list.
Definition PDCCH_ServingCellConfig__ext0O__F1 z :=
  (PDCCH_ServingCellConfig__ext0O__availabilityIndicator_r16 z, (PDCCH_ServingCellConfig__ext0O__searchSpaceSwitchTimer_r16 z, tt)).
Definition PDCCH_ServingCellConfig__ext0O__F2 (y : seq_type PDCCH_ServingCellConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDCCH_ServingCellConfig__ext0O__Type i0 i1
  end.
Lemma PDCCH_ServingCellConfig__ext0O__F1F2_cond (z : PDCCH_ServingCellConfig__ext0O__Type)
  : PDCCH_ServingCellConfig__ext0O__cond z ->
  (seq_cond PDCCH_ServingCellConfig__ext0O__list (PDCCH_ServingCellConfig__ext0O__F1 z)).
intro H. unfold PDCCH_ServingCellConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma PDCCH_ServingCellConfig__ext0O__F1F2_cond2 (z : PDCCH_ServingCellConfig__ext0O__Type)
 : PDCCH_ServingCellConfig__ext0O__F2 (PDCCH_ServingCellConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_ServingCellConfig__ext0O__F2F1_cond (y : seq_type PDCCH_ServingCellConfig__ext0O__list)
  : seq_cond PDCCH_ServingCellConfig__ext0O__list y ->
 (PDCCH_ServingCellConfig__ext0O__cond (PDCCH_ServingCellConfig__ext0O__F2 y)) /\  PDCCH_ServingCellConfig__ext0O__F1 (PDCCH_ServingCellConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_ServingCellConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold PDCCH_ServingCellConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_ServingCellConfig__ext0O__Format : T_Format PDCCH_ServingCellConfig__ext0O__Type PDCCH_ServingCellConfig__ext0O__cond :=
        proj2_format  PDCCH_ServingCellConfig__ext0O__cond PDCCH_ServingCellConfig__ext0O__list__Format
    PDCCH_ServingCellConfig__ext0O__F1 PDCCH_ServingCellConfig__ext0O__F2 PDCCH_ServingCellConfig__ext0O__F1F2_cond  PDCCH_ServingCellConfig__ext0O__F1F2_cond2 PDCCH_ServingCellConfig__ext0O__F2F1_cond.
Opaque PDCCH_ServingCellConfig__ext0O__cond PDCCH_ServingCellConfig__ext0O__Format.

Definition PDCCH_ServingCellConfig__ext0__check_all_none (b : PDCCH_ServingCellConfig__ext0O__Type) : bool :=
match b with 
  | make__PDCCH_ServingCellConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition PDCCH_ServingCellConfig__ext0__Format : T_Format PDCCH_ServingCellConfig__ext0__Type PDCCH_ServingCellConfig__ext0__cond :=
  restrict_add_format PDCCH_ServingCellConfig__ext0__check_all_none PDCCH_ServingCellConfig__ext0O__Format.

Opaque PDCCH_ServingCellConfig__ext0__cond PDCCH_ServingCellConfig__ext0__Format.

Definition PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__Format : T_Format Z PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__cond :=
 ranged_int_format (81) (1280) PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__helper1 PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__helper2.

Opaque PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__cond PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__Format.


Definition PDCCH_ServingCellConfig__ext1O__Format_Type := Eval cbn in seq_format_prod PDCCH_ServingCellConfig__ext1O__list.
Definition PDCCH_ServingCellConfig__ext1O__Format_list : PDCCH_ServingCellConfig__ext1O__Format_Type :=
  (PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710__Format, unit_format).
Definition PDCCH_ServingCellConfig__ext1O__list__Format := (*Eval compute in *) seq_format PDCCH_ServingCellConfig__ext1O__list PDCCH_ServingCellConfig__ext1O__Format_list.
Definition PDCCH_ServingCellConfig__ext1O__F1 z :=
  (PDCCH_ServingCellConfig__ext1O__searchSpaceSwitchTimer_v1710 z, tt).
Definition PDCCH_ServingCellConfig__ext1O__F2 (y : seq_type PDCCH_ServingCellConfig__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__PDCCH_ServingCellConfig__ext1O__Type i0
  end.
Lemma PDCCH_ServingCellConfig__ext1O__F1F2_cond (z : PDCCH_ServingCellConfig__ext1O__Type)
  : PDCCH_ServingCellConfig__ext1O__cond z ->
  (seq_cond PDCCH_ServingCellConfig__ext1O__list (PDCCH_ServingCellConfig__ext1O__F1 z)).
intro H. unfold PDCCH_ServingCellConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma PDCCH_ServingCellConfig__ext1O__F1F2_cond2 (z : PDCCH_ServingCellConfig__ext1O__Type)
 : PDCCH_ServingCellConfig__ext1O__F2 (PDCCH_ServingCellConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_ServingCellConfig__ext1O__F2F1_cond (y : seq_type PDCCH_ServingCellConfig__ext1O__list)
  : seq_cond PDCCH_ServingCellConfig__ext1O__list y ->
 (PDCCH_ServingCellConfig__ext1O__cond (PDCCH_ServingCellConfig__ext1O__F2 y)) /\  PDCCH_ServingCellConfig__ext1O__F1 (PDCCH_ServingCellConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_ServingCellConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold PDCCH_ServingCellConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_ServingCellConfig__ext1O__Format : T_Format PDCCH_ServingCellConfig__ext1O__Type PDCCH_ServingCellConfig__ext1O__cond :=
        proj2_format  PDCCH_ServingCellConfig__ext1O__cond PDCCH_ServingCellConfig__ext1O__list__Format
    PDCCH_ServingCellConfig__ext1O__F1 PDCCH_ServingCellConfig__ext1O__F2 PDCCH_ServingCellConfig__ext1O__F1F2_cond  PDCCH_ServingCellConfig__ext1O__F1F2_cond2 PDCCH_ServingCellConfig__ext1O__F2F1_cond.
Opaque PDCCH_ServingCellConfig__ext1O__cond PDCCH_ServingCellConfig__ext1O__Format.

Definition PDCCH_ServingCellConfig__ext1__check_all_none (b : PDCCH_ServingCellConfig__ext1O__Type) : bool :=
match b with 
  | make__PDCCH_ServingCellConfig__ext1O__Type None  => false 
  | _ => true 
 end.
Definition PDCCH_ServingCellConfig__ext1__Format : T_Format PDCCH_ServingCellConfig__ext1__Type PDCCH_ServingCellConfig__ext1__cond :=
  restrict_add_format PDCCH_ServingCellConfig__ext1__check_all_none PDCCH_ServingCellConfig__ext1O__Format.

Opaque PDCCH_ServingCellConfig__ext1__cond PDCCH_ServingCellConfig__ext1__Format.


Definition PDCCH_ServingCellConfig__root_Format_Type := Eval cbn in seq_format_prod PDCCH_ServingCellConfig__root_list.
Definition PDCCH_ServingCellConfig__root_Format_list : PDCCH_ServingCellConfig__root_Format_Type :=
  (PDCCH_ServingCellConfig__slotFormatIndicator__Format, unit_format).

Definition PDCCH_ServingCellConfig__ext_Format_Type := Eval cbn in get_formats PDCCH_ServingCellConfig__ext_list.
Definition PDCCH_ServingCellConfig__ext_Format_list : PDCCH_ServingCellConfig__ext_Format_Type :=
  (PDCCH_ServingCellConfig__ext0__Format, (PDCCH_ServingCellConfig__ext1__Format, unit__Format)).

Definition PDCCH_ServingCellConfig__list_type : Set := (seq_type PDCCH_ServingCellConfig__root_list) * (seq_ext_type PDCCH_ServingCellConfig__ext_list).
Definition PDCCH_ServingCellConfig__list_cond (z : PDCCH_ServingCellConfig__list_type) : Prop :=
        (seq_cond PDCCH_ServingCellConfig__root_list (fst z)) /\ (seq_ext_cond PDCCH_ServingCellConfig__ext_list (snd z)).
Definition PDCCH_ServingCellConfig__list_format : T_Format PDCCH_ServingCellConfig__list_type PDCCH_ServingCellConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PDCCH_ServingCellConfig__root_list PDCCH_ServingCellConfig__root_Format_list PDCCH_ServingCellConfig__ext_list PDCCH_ServingCellConfig__ext_Format_list.

Opaque PDCCH_ServingCellConfig__list_format.
Definition PDCCH_ServingCellConfig__F1 (z : PDCCH_ServingCellConfig__Type) : PDCCH_ServingCellConfig__list_type :=
  (((PDCCH_ServingCellConfig__slotFormatIndicator z, tt)), (
(PDCCH_ServingCellConfig__ext0 z, (PDCCH_ServingCellConfig__ext1 z, tt)))).
Definition PDCCH_ServingCellConfig__F2 (y : PDCCH_ServingCellConfig__list_type) : PDCCH_ServingCellConfig__Type :=
  match y with
  | ((j0, _), (i0, (i1, _)))=>
    make__PDCCH_ServingCellConfig__Type j0 i0 i1
  end.
Definition PDCCH_ServingCellConfig__helper1 : (forall a : PDCCH_ServingCellConfig__Type, PDCCH_ServingCellConfig__cond a -> PDCCH_ServingCellConfig__list_cond (PDCCH_ServingCellConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDCCH_ServingCellConfig__helper2 : (forall a : PDCCH_ServingCellConfig__Type, PDCCH_ServingCellConfig__F2 (PDCCH_ServingCellConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDCCH_ServingCellConfig__helper3 : (forall b : PDCCH_ServingCellConfig__list_type, PDCCH_ServingCellConfig__list_cond b -> PDCCH_ServingCellConfig__cond (PDCCH_ServingCellConfig__F2 b) /\ PDCCH_ServingCellConfig__F1 (PDCCH_ServingCellConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDCCH_ServingCellConfig__cond, PDCCH_ServingCellConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDCCH_ServingCellConfig__Format : T_Format PDCCH_ServingCellConfig__Type PDCCH_ServingCellConfig__cond :=
 proj2_format PDCCH_ServingCellConfig__cond PDCCH_ServingCellConfig__list_format  PDCCH_ServingCellConfig__F1 PDCCH_ServingCellConfig__F2 PDCCH_ServingCellConfig__helper1 PDCCH_ServingCellConfig__helper2 PDCCH_ServingCellConfig__helper3.

Opaque PDCCH_ServingCellConfig__cond PDCCH_ServingCellConfig__Format.

