Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_RemoteUE_ToAddMod_r17.

Opaque SL_RemoteUE_ToAddMod_r17__cond SL_RemoteUE_ToAddMod_r17__Format.

Definition SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__Type := list SL_RemoteUE_ToAddMod_r17__Type.

Lemma SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__helper1 : (0 <= 1 <= maxNrofRemoteUE_r17)%Z. unfold maxNrofRemoteUE_r17.
 lia. Qed.
Lemma SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofRemoteUE_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRemoteUE_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__cond (z : SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRemoteUE_r17)%Z /\ (list_and SL_RemoteUE_ToAddMod_r17__cond z) .

Require Import NR.SL_DestinationIdentity_r16.

Opaque SL_DestinationIdentity_r16__cond SL_DestinationIdentity_r16__Format.

Definition SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__Type := list SL_DestinationIdentity_r16__Type.

Lemma SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofRemoteUE_r17)%Z. unfold maxNrofRemoteUE_r17.
 lia. Qed.
Lemma SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofRemoteUE_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRemoteUE_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__cond (z : SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRemoteUE_r17)%Z /\ (list_and SL_DestinationIdentity_r16__cond z) .

Record SL_L2RelayUE_Config_r17__Type : Set :=
  make__SL_L2RelayUE_Config_r17__Type {
    SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17 : option SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__Type ;
    SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17 : option SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__Type ;
}.
Definition SL_L2RelayUE_Config_r17__root_list : list seq_elem := (
 Opt SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__Type SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__cond ::
 Opt SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__Type SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__cond ::
 nil).
Definition SL_L2RelayUE_Config_r17__ext_list : list typ := (
  nil).
Definition SL_L2RelayUE_Config_r17__cond (z : SL_L2RelayUE_Config_r17__Type) := 
(  opt_cond SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__cond (SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17 z) /\
  opt_cond SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__cond (SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17 z) /\
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
Definition SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__Format : T_Format SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__Type SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__cond := seq_of_format SL_RemoteUE_ToAddMod_r17__Format 1 maxNrofRemoteUE_r17 SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__helper1 SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__helper2.

Opaque SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__cond SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__Format.

Definition SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__Format : T_Format SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__Type SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__cond := seq_of_format SL_DestinationIdentity_r16__Format 1 maxNrofRemoteUE_r17 SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__helper1 SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__helper2.

Opaque SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__cond SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__Format.


Definition SL_L2RelayUE_Config_r17__root_Format_Type := Eval cbn in seq_format_prod SL_L2RelayUE_Config_r17__root_list.
Definition SL_L2RelayUE_Config_r17__root_Format_list : SL_L2RelayUE_Config_r17__root_Format_Type :=
  (SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17__Format, (SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17__Format, unit_format)).

Definition SL_L2RelayUE_Config_r17__ext_Format_Type := Eval cbn in get_formats SL_L2RelayUE_Config_r17__ext_list.
Definition SL_L2RelayUE_Config_r17__ext_Format_list : SL_L2RelayUE_Config_r17__ext_Format_Type :=
  unit__Format.

Definition SL_L2RelayUE_Config_r17__list_type : Set := (seq_type SL_L2RelayUE_Config_r17__root_list) * (seq_ext_type SL_L2RelayUE_Config_r17__ext_list).
Definition SL_L2RelayUE_Config_r17__list_cond (z : SL_L2RelayUE_Config_r17__list_type) : Prop :=
        (seq_cond SL_L2RelayUE_Config_r17__root_list (fst z)) /\ (seq_ext_cond SL_L2RelayUE_Config_r17__ext_list (snd z)).
Definition SL_L2RelayUE_Config_r17__list_format : T_Format SL_L2RelayUE_Config_r17__list_type SL_L2RelayUE_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SL_L2RelayUE_Config_r17__root_list SL_L2RelayUE_Config_r17__root_Format_list SL_L2RelayUE_Config_r17__ext_list SL_L2RelayUE_Config_r17__ext_Format_list.

Opaque SL_L2RelayUE_Config_r17__list_format.
Definition SL_L2RelayUE_Config_r17__F1 (z : SL_L2RelayUE_Config_r17__Type) : SL_L2RelayUE_Config_r17__list_type :=
  (((SL_L2RelayUE_Config_r17__sl_RemoteUE_ToAddModList_r17 z, (SL_L2RelayUE_Config_r17__sl_RemoteUE_ToReleaseList_r17 z, tt))), (
tt)).
Definition SL_L2RelayUE_Config_r17__F2 (y : SL_L2RelayUE_Config_r17__list_type) : SL_L2RelayUE_Config_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__SL_L2RelayUE_Config_r17__Type j0 j1
  end.
Definition SL_L2RelayUE_Config_r17__helper1 : (forall a : SL_L2RelayUE_Config_r17__Type, SL_L2RelayUE_Config_r17__cond a -> SL_L2RelayUE_Config_r17__list_cond (SL_L2RelayUE_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_L2RelayUE_Config_r17__helper2 : (forall a : SL_L2RelayUE_Config_r17__Type, SL_L2RelayUE_Config_r17__F2 (SL_L2RelayUE_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_L2RelayUE_Config_r17__helper3 : (forall b : SL_L2RelayUE_Config_r17__list_type, SL_L2RelayUE_Config_r17__list_cond b -> SL_L2RelayUE_Config_r17__cond (SL_L2RelayUE_Config_r17__F2 b) /\ SL_L2RelayUE_Config_r17__F1 (SL_L2RelayUE_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_L2RelayUE_Config_r17__cond, SL_L2RelayUE_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_L2RelayUE_Config_r17__Format : T_Format SL_L2RelayUE_Config_r17__Type SL_L2RelayUE_Config_r17__cond :=
 proj2_format SL_L2RelayUE_Config_r17__cond SL_L2RelayUE_Config_r17__list_format  SL_L2RelayUE_Config_r17__F1 SL_L2RelayUE_Config_r17__F2 SL_L2RelayUE_Config_r17__helper1 SL_L2RelayUE_Config_r17__helper2 SL_L2RelayUE_Config_r17__helper3.

Opaque SL_L2RelayUE_Config_r17__cond SL_L2RelayUE_Config_r17__Format.

