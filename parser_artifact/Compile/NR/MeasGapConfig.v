Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.GapConfig.
Definition MeasGapConfig__gapFR2__Type := SetupRelease__Type GapConfig__Type.
Definition MeasGapConfig__gapFR2__cond := SetupRelease__cond _ GapConfig__cond.
Definition MeasGapConfig__gapFR2__Format : T_Format MeasGapConfig__gapFR2__Type MeasGapConfig__gapFR2__cond := SetupRelease__Format _ _ GapConfig__Format.
Opaque MeasGapConfig__gapFR2__cond MeasGapConfig__gapFR2__Format.

Require Import NR.SetupRelease.
Require Import NR.GapConfig.
Definition MeasGapConfig__ext0O__gapFR1__Type := SetupRelease__Type GapConfig__Type.
Definition MeasGapConfig__ext0O__gapFR1__cond := SetupRelease__cond _ GapConfig__cond.
Definition MeasGapConfig__ext0O__gapFR1__Format : T_Format MeasGapConfig__ext0O__gapFR1__Type MeasGapConfig__ext0O__gapFR1__cond := SetupRelease__Format _ _ GapConfig__Format.
Opaque MeasGapConfig__ext0O__gapFR1__cond MeasGapConfig__ext0O__gapFR1__Format.

Require Import NR.SetupRelease.
Require Import NR.GapConfig.
Definition MeasGapConfig__ext0O__gapUE__Type := SetupRelease__Type GapConfig__Type.
Definition MeasGapConfig__ext0O__gapUE__cond := SetupRelease__cond _ GapConfig__cond.
Definition MeasGapConfig__ext0O__gapUE__Format : T_Format MeasGapConfig__ext0O__gapUE__Type MeasGapConfig__ext0O__gapUE__cond := SetupRelease__Format _ _ GapConfig__Format.
Opaque MeasGapConfig__ext0O__gapUE__cond MeasGapConfig__ext0O__gapUE__Format.

Record MeasGapConfig__ext0O__Type : Set :=
  make__MeasGapConfig__ext0O__Type {
    MeasGapConfig__ext0O__gapFR1 : option MeasGapConfig__ext0O__gapFR1__Type ;
    MeasGapConfig__ext0O__gapUE : option MeasGapConfig__ext0O__gapUE__Type ;
}.
Definition MeasGapConfig__ext0O__list := (
 Opt MeasGapConfig__ext0O__gapFR1__Type MeasGapConfig__ext0O__gapFR1__cond ::
 Opt MeasGapConfig__ext0O__gapUE__Type MeasGapConfig__ext0O__gapUE__cond ::
 nil).
Definition MeasGapConfig__ext0O__cond z := 
  opt_cond MeasGapConfig__ext0O__gapFR1__cond (MeasGapConfig__ext0O__gapFR1 z) /\
  opt_cond MeasGapConfig__ext0O__gapUE__cond (MeasGapConfig__ext0O__gapUE z) /\
  True.

Definition MeasGapConfig__ext0__Type := MeasGapConfig__ext0O__Type.
Definition MeasGapConfig__ext0__cond := MeasGapConfig__ext0O__cond.

Require Import NR.GapConfig_r17.

Opaque GapConfig_r17__cond GapConfig_r17__Format.

Definition MeasGapConfig__ext1O__gapToAddModList_r17__Type := list GapConfig_r17__Type.

Lemma MeasGapConfig__ext1O__gapToAddModList_r17__helper1 : (0 <= 1 <= maxNrofGapId_r17)%Z. unfold maxNrofGapId_r17.
 lia. Qed.
Lemma MeasGapConfig__ext1O__gapToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofGapId_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofGapId_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasGapConfig__ext1O__gapToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasGapConfig__ext1O__gapToAddModList_r17__cond (z : MeasGapConfig__ext1O__gapToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofGapId_r17)%Z /\ (list_and GapConfig_r17__cond z) .

Require Import NR.MeasGapId_r17.

Opaque MeasGapId_r17__cond MeasGapId_r17__Format.

Definition MeasGapConfig__ext1O__gapToReleaseList_r17__Type := list MeasGapId_r17__Type.

Lemma MeasGapConfig__ext1O__gapToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofGapId_r17)%Z. unfold maxNrofGapId_r17.
 lia. Qed.
Lemma MeasGapConfig__ext1O__gapToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofGapId_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofGapId_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasGapConfig__ext1O__gapToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasGapConfig__ext1O__gapToReleaseList_r17__cond (z : MeasGapConfig__ext1O__gapToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofGapId_r17)%Z /\ (list_and MeasGapId_r17__cond z) .

Require Import NR.PosMeasGapPreConfigToAddModList_r17.

Opaque PosMeasGapPreConfigToAddModList_r17__cond PosMeasGapPreConfigToAddModList_r17__Format.

Require Import NR.PosMeasGapPreConfigToReleaseList_r17.

Opaque PosMeasGapPreConfigToReleaseList_r17__cond PosMeasGapPreConfigToReleaseList_r17__Format.

Record MeasGapConfig__ext1O__Type : Set :=
  make__MeasGapConfig__ext1O__Type {
    MeasGapConfig__ext1O__gapToAddModList_r17 : option MeasGapConfig__ext1O__gapToAddModList_r17__Type ;
    MeasGapConfig__ext1O__gapToReleaseList_r17 : option MeasGapConfig__ext1O__gapToReleaseList_r17__Type ;
    MeasGapConfig__ext1O__posMeasGapPreConfigToAddModList_r17 : option PosMeasGapPreConfigToAddModList_r17__Type ;
    MeasGapConfig__ext1O__posMeasGapPreConfigToReleaseList_r17 : option PosMeasGapPreConfigToReleaseList_r17__Type ;
}.
Definition MeasGapConfig__ext1O__list := (
 Opt MeasGapConfig__ext1O__gapToAddModList_r17__Type MeasGapConfig__ext1O__gapToAddModList_r17__cond ::
 Opt MeasGapConfig__ext1O__gapToReleaseList_r17__Type MeasGapConfig__ext1O__gapToReleaseList_r17__cond ::
 Opt PosMeasGapPreConfigToAddModList_r17__Type PosMeasGapPreConfigToAddModList_r17__cond ::
 Opt PosMeasGapPreConfigToReleaseList_r17__Type PosMeasGapPreConfigToReleaseList_r17__cond ::
 nil).
Definition MeasGapConfig__ext1O__cond z := 
  opt_cond MeasGapConfig__ext1O__gapToAddModList_r17__cond (MeasGapConfig__ext1O__gapToAddModList_r17 z) /\
  opt_cond MeasGapConfig__ext1O__gapToReleaseList_r17__cond (MeasGapConfig__ext1O__gapToReleaseList_r17 z) /\
  opt_cond PosMeasGapPreConfigToAddModList_r17__cond (MeasGapConfig__ext1O__posMeasGapPreConfigToAddModList_r17 z) /\
  opt_cond PosMeasGapPreConfigToReleaseList_r17__cond (MeasGapConfig__ext1O__posMeasGapPreConfigToReleaseList_r17 z) /\
  True.

Definition MeasGapConfig__ext1__Type := MeasGapConfig__ext1O__Type.
Definition MeasGapConfig__ext1__cond := MeasGapConfig__ext1O__cond.

Record MeasGapConfig__Type : Set :=
  make__MeasGapConfig__Type {
    MeasGapConfig__gapFR2 : option MeasGapConfig__gapFR2__Type ;
    MeasGapConfig__ext0 : option MeasGapConfig__ext0__Type ;
    MeasGapConfig__ext1 : option MeasGapConfig__ext1__Type ;
}.
Definition MeasGapConfig__root_list : list seq_elem := (
 Opt MeasGapConfig__gapFR2__Type MeasGapConfig__gapFR2__cond ::
 nil).
Definition MeasGapConfig__ext_list : list typ := (
  typ_cons MeasGapConfig__ext0__Type MeasGapConfig__ext0__cond ::
  typ_cons MeasGapConfig__ext1__Type MeasGapConfig__ext1__cond ::
  nil).
Definition MeasGapConfig__cond (z : MeasGapConfig__Type) := 
(  opt_cond MeasGapConfig__gapFR2__cond (MeasGapConfig__gapFR2 z) /\
  True) /\ 
(  opt_cond MeasGapConfig__ext0__cond (MeasGapConfig__ext0 z) /\
  opt_cond MeasGapConfig__ext1__cond (MeasGapConfig__ext1 z) /\
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
Opaque MeasGapConfig__gapFR2__cond MeasGapConfig__gapFR2__Format.

Opaque MeasGapConfig__ext0O__gapFR1__cond MeasGapConfig__ext0O__gapFR1__Format.

Opaque MeasGapConfig__ext0O__gapUE__cond MeasGapConfig__ext0O__gapUE__Format.


Definition MeasGapConfig__ext0O__Format_Type := Eval cbn in seq_format_prod MeasGapConfig__ext0O__list.
Definition MeasGapConfig__ext0O__Format_list : MeasGapConfig__ext0O__Format_Type :=
  (MeasGapConfig__ext0O__gapFR1__Format, (MeasGapConfig__ext0O__gapUE__Format, unit_format)).
Definition MeasGapConfig__ext0O__list__Format := (*Eval compute in *) seq_format MeasGapConfig__ext0O__list MeasGapConfig__ext0O__Format_list.
Definition MeasGapConfig__ext0O__F1 z :=
  (MeasGapConfig__ext0O__gapFR1 z, (MeasGapConfig__ext0O__gapUE z, tt)).
Definition MeasGapConfig__ext0O__F2 (y : seq_type MeasGapConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasGapConfig__ext0O__Type i0 i1
  end.
Lemma MeasGapConfig__ext0O__F1F2_cond (z : MeasGapConfig__ext0O__Type)
  : MeasGapConfig__ext0O__cond z ->
  (seq_cond MeasGapConfig__ext0O__list (MeasGapConfig__ext0O__F1 z)).
intro H. unfold MeasGapConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasGapConfig__ext0O__F1F2_cond2 (z : MeasGapConfig__ext0O__Type)
 : MeasGapConfig__ext0O__F2 (MeasGapConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasGapConfig__ext0O__F2F1_cond (y : seq_type MeasGapConfig__ext0O__list)
  : seq_cond MeasGapConfig__ext0O__list y ->
 (MeasGapConfig__ext0O__cond (MeasGapConfig__ext0O__F2 y)) /\  MeasGapConfig__ext0O__F1 (MeasGapConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasGapConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasGapConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasGapConfig__ext0O__Format : T_Format MeasGapConfig__ext0O__Type MeasGapConfig__ext0O__cond :=
        proj2_format  MeasGapConfig__ext0O__cond MeasGapConfig__ext0O__list__Format
    MeasGapConfig__ext0O__F1 MeasGapConfig__ext0O__F2 MeasGapConfig__ext0O__F1F2_cond  MeasGapConfig__ext0O__F1F2_cond2 MeasGapConfig__ext0O__F2F1_cond.
Opaque MeasGapConfig__ext0O__cond MeasGapConfig__ext0O__Format.

Definition MeasGapConfig__ext0__check_all_none (b : MeasGapConfig__ext0O__Type) : bool :=
match b with 
  | make__MeasGapConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition MeasGapConfig__ext0__Format : T_Format MeasGapConfig__ext0__Type MeasGapConfig__ext0__cond :=
  restrict_add_format MeasGapConfig__ext0__check_all_none MeasGapConfig__ext0O__Format.

Opaque MeasGapConfig__ext0__cond MeasGapConfig__ext0__Format.

Definition MeasGapConfig__ext1O__gapToAddModList_r17__Format : T_Format MeasGapConfig__ext1O__gapToAddModList_r17__Type MeasGapConfig__ext1O__gapToAddModList_r17__cond := seq_of_format GapConfig_r17__Format 1 maxNrofGapId_r17 MeasGapConfig__ext1O__gapToAddModList_r17__helper1 MeasGapConfig__ext1O__gapToAddModList_r17__helper2.

Opaque MeasGapConfig__ext1O__gapToAddModList_r17__cond MeasGapConfig__ext1O__gapToAddModList_r17__Format.

Definition MeasGapConfig__ext1O__gapToReleaseList_r17__Format : T_Format MeasGapConfig__ext1O__gapToReleaseList_r17__Type MeasGapConfig__ext1O__gapToReleaseList_r17__cond := seq_of_format MeasGapId_r17__Format 1 maxNrofGapId_r17 MeasGapConfig__ext1O__gapToReleaseList_r17__helper1 MeasGapConfig__ext1O__gapToReleaseList_r17__helper2.

Opaque MeasGapConfig__ext1O__gapToReleaseList_r17__cond MeasGapConfig__ext1O__gapToReleaseList_r17__Format.


Definition MeasGapConfig__ext1O__Format_Type := Eval cbn in seq_format_prod MeasGapConfig__ext1O__list.
Definition MeasGapConfig__ext1O__Format_list : MeasGapConfig__ext1O__Format_Type :=
  (MeasGapConfig__ext1O__gapToAddModList_r17__Format, (MeasGapConfig__ext1O__gapToReleaseList_r17__Format, (PosMeasGapPreConfigToAddModList_r17__Format, (PosMeasGapPreConfigToReleaseList_r17__Format, unit_format)))).
Definition MeasGapConfig__ext1O__list__Format := (*Eval compute in *) seq_format MeasGapConfig__ext1O__list MeasGapConfig__ext1O__Format_list.
Definition MeasGapConfig__ext1O__F1 z :=
  (MeasGapConfig__ext1O__gapToAddModList_r17 z, (MeasGapConfig__ext1O__gapToReleaseList_r17 z, (MeasGapConfig__ext1O__posMeasGapPreConfigToAddModList_r17 z, (MeasGapConfig__ext1O__posMeasGapPreConfigToReleaseList_r17 z, tt)))).
Definition MeasGapConfig__ext1O__F2 (y : seq_type MeasGapConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasGapConfig__ext1O__Type i0 i1 i2 i3
  end.
Lemma MeasGapConfig__ext1O__F1F2_cond (z : MeasGapConfig__ext1O__Type)
  : MeasGapConfig__ext1O__cond z ->
  (seq_cond MeasGapConfig__ext1O__list (MeasGapConfig__ext1O__F1 z)).
intro H. unfold MeasGapConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma MeasGapConfig__ext1O__F1F2_cond2 (z : MeasGapConfig__ext1O__Type)
 : MeasGapConfig__ext1O__F2 (MeasGapConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasGapConfig__ext1O__F2F1_cond (y : seq_type MeasGapConfig__ext1O__list)
  : seq_cond MeasGapConfig__ext1O__list y ->
 (MeasGapConfig__ext1O__cond (MeasGapConfig__ext1O__F2 y)) /\  MeasGapConfig__ext1O__F1 (MeasGapConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasGapConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold MeasGapConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasGapConfig__ext1O__Format : T_Format MeasGapConfig__ext1O__Type MeasGapConfig__ext1O__cond :=
        proj2_format  MeasGapConfig__ext1O__cond MeasGapConfig__ext1O__list__Format
    MeasGapConfig__ext1O__F1 MeasGapConfig__ext1O__F2 MeasGapConfig__ext1O__F1F2_cond  MeasGapConfig__ext1O__F1F2_cond2 MeasGapConfig__ext1O__F2F1_cond.
Opaque MeasGapConfig__ext1O__cond MeasGapConfig__ext1O__Format.

Definition MeasGapConfig__ext1__check_all_none (b : MeasGapConfig__ext1O__Type) : bool :=
match b with 
  | make__MeasGapConfig__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition MeasGapConfig__ext1__Format : T_Format MeasGapConfig__ext1__Type MeasGapConfig__ext1__cond :=
  restrict_add_format MeasGapConfig__ext1__check_all_none MeasGapConfig__ext1O__Format.

Opaque MeasGapConfig__ext1__cond MeasGapConfig__ext1__Format.


Definition MeasGapConfig__root_Format_Type := Eval cbn in seq_format_prod MeasGapConfig__root_list.
Definition MeasGapConfig__root_Format_list : MeasGapConfig__root_Format_Type :=
  (MeasGapConfig__gapFR2__Format, unit_format).

Definition MeasGapConfig__ext_Format_Type := Eval cbn in get_formats MeasGapConfig__ext_list.
Definition MeasGapConfig__ext_Format_list : MeasGapConfig__ext_Format_Type :=
  (MeasGapConfig__ext0__Format, (MeasGapConfig__ext1__Format, unit__Format)).

Definition MeasGapConfig__list_type : Set := (seq_type MeasGapConfig__root_list) * (seq_ext_type MeasGapConfig__ext_list).
Definition MeasGapConfig__list_cond (z : MeasGapConfig__list_type) : Prop :=
        (seq_cond MeasGapConfig__root_list (fst z)) /\ (seq_ext_cond MeasGapConfig__ext_list (snd z)).
Definition MeasGapConfig__list_format : T_Format MeasGapConfig__list_type MeasGapConfig__list_cond :=
 (* Eval compute in *) seq_ext_format MeasGapConfig__root_list MeasGapConfig__root_Format_list MeasGapConfig__ext_list MeasGapConfig__ext_Format_list.

Opaque MeasGapConfig__list_format.
Definition MeasGapConfig__F1 (z : MeasGapConfig__Type) : MeasGapConfig__list_type :=
  (((MeasGapConfig__gapFR2 z, tt)), (
(MeasGapConfig__ext0 z, (MeasGapConfig__ext1 z, tt)))).
Definition MeasGapConfig__F2 (y : MeasGapConfig__list_type) : MeasGapConfig__Type :=
  match y with
  | ((j0, _), (i0, (i1, _)))=>
    make__MeasGapConfig__Type j0 i0 i1
  end.
Definition MeasGapConfig__helper1 : (forall a : MeasGapConfig__Type, MeasGapConfig__cond a -> MeasGapConfig__list_cond (MeasGapConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasGapConfig__helper2 : (forall a : MeasGapConfig__Type, MeasGapConfig__F2 (MeasGapConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasGapConfig__helper3 : (forall b : MeasGapConfig__list_type, MeasGapConfig__list_cond b -> MeasGapConfig__cond (MeasGapConfig__F2 b) /\ MeasGapConfig__F1 (MeasGapConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasGapConfig__cond, MeasGapConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasGapConfig__Format : T_Format MeasGapConfig__Type MeasGapConfig__cond :=
 proj2_format MeasGapConfig__cond MeasGapConfig__list_format  MeasGapConfig__F1 MeasGapConfig__F2 MeasGapConfig__helper1 MeasGapConfig__helper2 MeasGapConfig__helper3.

Opaque MeasGapConfig__cond MeasGapConfig__Format.

