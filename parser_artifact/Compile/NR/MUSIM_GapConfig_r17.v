Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MUSIM_GapId_r17.

Opaque MUSIM_GapId_r17__cond MUSIM_GapId_r17__Format.

Definition MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__Type := list MUSIM_GapId_r17__Type.

Lemma MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__helper1 : (0 <= 1 <= 3)%Z.  lia. Qed.
Lemma MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__cond (z : MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= 3)%Z /\ (list_and MUSIM_GapId_r17__cond z) .

Require Import NR.MUSIM_Gap_r17.

Opaque MUSIM_Gap_r17__cond MUSIM_Gap_r17__Format.

Definition MUSIM_GapConfig_r17__musim_GapToAddModList_r17__Type := list MUSIM_Gap_r17__Type.

Lemma MUSIM_GapConfig_r17__musim_GapToAddModList_r17__helper1 : (0 <= 1 <= 3)%Z.  lia. Qed.
Lemma MUSIM_GapConfig_r17__musim_GapToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapConfig_r17__musim_GapToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapConfig_r17__musim_GapToAddModList_r17__cond (z : MUSIM_GapConfig_r17__musim_GapToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= 3)%Z /\ (list_and MUSIM_Gap_r17__cond z) .

Require Import NR.MUSIM_GapInfo_r17.

Opaque MUSIM_GapInfo_r17__cond MUSIM_GapInfo_r17__Format.

Record MUSIM_GapConfig_r17__Type : Set :=
  make__MUSIM_GapConfig_r17__Type {
    MUSIM_GapConfig_r17__musim_GapToReleaseList_r17 : option MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__Type ;
    MUSIM_GapConfig_r17__musim_GapToAddModList_r17 : option MUSIM_GapConfig_r17__musim_GapToAddModList_r17__Type ;
    MUSIM_GapConfig_r17__musim_AperiodicGap_r17 : option MUSIM_GapInfo_r17__Type ;
}.
Definition MUSIM_GapConfig_r17__root_list : list seq_elem := (
 Opt MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__Type MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__cond ::
 Opt MUSIM_GapConfig_r17__musim_GapToAddModList_r17__Type MUSIM_GapConfig_r17__musim_GapToAddModList_r17__cond ::
 Opt MUSIM_GapInfo_r17__Type MUSIM_GapInfo_r17__cond ::
 nil).
Definition MUSIM_GapConfig_r17__ext_list : list typ := (
  nil).
Definition MUSIM_GapConfig_r17__cond (z : MUSIM_GapConfig_r17__Type) := 
(  opt_cond MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__cond (MUSIM_GapConfig_r17__musim_GapToReleaseList_r17 z) /\
  opt_cond MUSIM_GapConfig_r17__musim_GapToAddModList_r17__cond (MUSIM_GapConfig_r17__musim_GapToAddModList_r17 z) /\
  opt_cond MUSIM_GapInfo_r17__cond (MUSIM_GapConfig_r17__musim_AperiodicGap_r17 z) /\
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
Definition MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__Format : T_Format MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__Type MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__cond := seq_of_format MUSIM_GapId_r17__Format 1 3 MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__helper1 MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__helper2.

Opaque MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__cond MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__Format.

Definition MUSIM_GapConfig_r17__musim_GapToAddModList_r17__Format : T_Format MUSIM_GapConfig_r17__musim_GapToAddModList_r17__Type MUSIM_GapConfig_r17__musim_GapToAddModList_r17__cond := seq_of_format MUSIM_Gap_r17__Format 1 3 MUSIM_GapConfig_r17__musim_GapToAddModList_r17__helper1 MUSIM_GapConfig_r17__musim_GapToAddModList_r17__helper2.

Opaque MUSIM_GapConfig_r17__musim_GapToAddModList_r17__cond MUSIM_GapConfig_r17__musim_GapToAddModList_r17__Format.


Definition MUSIM_GapConfig_r17__root_Format_Type := Eval cbn in seq_format_prod MUSIM_GapConfig_r17__root_list.
Definition MUSIM_GapConfig_r17__root_Format_list : MUSIM_GapConfig_r17__root_Format_Type :=
  (MUSIM_GapConfig_r17__musim_GapToReleaseList_r17__Format, (MUSIM_GapConfig_r17__musim_GapToAddModList_r17__Format, (MUSIM_GapInfo_r17__Format, unit_format))).

Definition MUSIM_GapConfig_r17__ext_Format_Type := Eval cbn in get_formats MUSIM_GapConfig_r17__ext_list.
Definition MUSIM_GapConfig_r17__ext_Format_list : MUSIM_GapConfig_r17__ext_Format_Type :=
  unit__Format.

Definition MUSIM_GapConfig_r17__list_type : Set := (seq_type MUSIM_GapConfig_r17__root_list) * (seq_ext_type MUSIM_GapConfig_r17__ext_list).
Definition MUSIM_GapConfig_r17__list_cond (z : MUSIM_GapConfig_r17__list_type) : Prop :=
        (seq_cond MUSIM_GapConfig_r17__root_list (fst z)) /\ (seq_ext_cond MUSIM_GapConfig_r17__ext_list (snd z)).
Definition MUSIM_GapConfig_r17__list_format : T_Format MUSIM_GapConfig_r17__list_type MUSIM_GapConfig_r17__list_cond :=
 (* Eval compute in *) seq_ext_format MUSIM_GapConfig_r17__root_list MUSIM_GapConfig_r17__root_Format_list MUSIM_GapConfig_r17__ext_list MUSIM_GapConfig_r17__ext_Format_list.

Opaque MUSIM_GapConfig_r17__list_format.
Definition MUSIM_GapConfig_r17__F1 (z : MUSIM_GapConfig_r17__Type) : MUSIM_GapConfig_r17__list_type :=
  (((MUSIM_GapConfig_r17__musim_GapToReleaseList_r17 z, (MUSIM_GapConfig_r17__musim_GapToAddModList_r17 z, (MUSIM_GapConfig_r17__musim_AperiodicGap_r17 z, tt)))), (
tt)).
Definition MUSIM_GapConfig_r17__F2 (y : MUSIM_GapConfig_r17__list_type) : MUSIM_GapConfig_r17__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__MUSIM_GapConfig_r17__Type j0 j1 j2
  end.
Definition MUSIM_GapConfig_r17__helper1 : (forall a : MUSIM_GapConfig_r17__Type, MUSIM_GapConfig_r17__cond a -> MUSIM_GapConfig_r17__list_cond (MUSIM_GapConfig_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MUSIM_GapConfig_r17__helper2 : (forall a : MUSIM_GapConfig_r17__Type, MUSIM_GapConfig_r17__F2 (MUSIM_GapConfig_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MUSIM_GapConfig_r17__helper3 : (forall b : MUSIM_GapConfig_r17__list_type, MUSIM_GapConfig_r17__list_cond b -> MUSIM_GapConfig_r17__cond (MUSIM_GapConfig_r17__F2 b) /\ MUSIM_GapConfig_r17__F1 (MUSIM_GapConfig_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MUSIM_GapConfig_r17__cond, MUSIM_GapConfig_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MUSIM_GapConfig_r17__Format : T_Format MUSIM_GapConfig_r17__Type MUSIM_GapConfig_r17__cond :=
 proj2_format MUSIM_GapConfig_r17__cond MUSIM_GapConfig_r17__list_format  MUSIM_GapConfig_r17__F1 MUSIM_GapConfig_r17__F2 MUSIM_GapConfig_r17__helper1 MUSIM_GapConfig_r17__helper2 MUSIM_GapConfig_r17__helper3.

Opaque MUSIM_GapConfig_r17__cond MUSIM_GapConfig_r17__Format.

