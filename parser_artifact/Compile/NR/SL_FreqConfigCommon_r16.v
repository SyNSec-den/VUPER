Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SCS_SpecificCarrier.

Opaque SCS_SpecificCarrier__cond SCS_SpecificCarrier__Format.

Definition SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__Type := list SCS_SpecificCarrier__Type.

Lemma SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__cond (z : SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SCS_SpecificCarrier__cond z) .

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Inductive SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Type : Set :=
 | SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__true
.
Definition SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__cond := (fun (_ : SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Type) => True).
Lemma SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__nat__helper.

Definition SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F1 t :=
  match t with
  | SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__true => 0
  end.
Definition SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F2 n :=
  match n with
  | 0 => SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__true
  | _ => SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__true
  end.
Lemma SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F1F2 : forall x : SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Type, (SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F1 x <= 0) /\ SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F2 (SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F1 (SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_FreqConfigCommon_r16__valueN_r16__helper1 : (-1 <= 1)%Z.  lia. Qed.
Lemma SL_FreqConfigCommon_r16__valueN_r16__helper2 : to_bit_sz (Z.to_nat (1 - -1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - -1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_FreqConfigCommon_r16__valueN_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_FreqConfigCommon_r16__valueN_r16__Type := Z.
Definition SL_FreqConfigCommon_r16__valueN_r16__cond := (fun z => (-1 <= z <= 1)%Z).
Require Import NR.SL_BWP_ConfigCommon_r16.

Opaque SL_BWP_ConfigCommon_r16__cond SL_BWP_ConfigCommon_r16__Format.

Definition SL_FreqConfigCommon_r16__sl_BWP_List_r16__Type := list SL_BWP_ConfigCommon_r16__Type.

Lemma SL_FreqConfigCommon_r16__sl_BWP_List_r16__helper1 : (0 <= 1 <= maxNrofSL_BWPs_r16)%Z. unfold maxNrofSL_BWPs_r16.
 lia. Qed.
Lemma SL_FreqConfigCommon_r16__sl_BWP_List_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_BWPs_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_BWPs_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_FreqConfigCommon_r16__sl_BWP_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_FreqConfigCommon_r16__sl_BWP_List_r16__cond (z : SL_FreqConfigCommon_r16__sl_BWP_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_BWPs_r16)%Z /\ (list_and SL_BWP_ConfigCommon_r16__cond z) .

Inductive SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Type : Set :=
 | SL_FreqConfigCommon_r16__sl_SyncPriority_r16__gnss
 | SL_FreqConfigCommon_r16__sl_SyncPriority_r16__gnbEnb
.
Definition SL_FreqConfigCommon_r16__sl_SyncPriority_r16__cond := (fun (_ : SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Type) => True).
Lemma SL_FreqConfigCommon_r16__sl_SyncPriority_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_FreqConfigCommon_r16__sl_SyncPriority_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_FreqConfigCommon_r16__sl_SyncPriority_r16__nat__helper.

Definition SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F1 t :=
  match t with
  | SL_FreqConfigCommon_r16__sl_SyncPriority_r16__gnss => 0
  | SL_FreqConfigCommon_r16__sl_SyncPriority_r16__gnbEnb => 1
  end.
Definition SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F2 n :=
  match n with
  | 0 => SL_FreqConfigCommon_r16__sl_SyncPriority_r16__gnss
  | 1 => SL_FreqConfigCommon_r16__sl_SyncPriority_r16__gnbEnb
  | _ => SL_FreqConfigCommon_r16__sl_SyncPriority_r16__gnss
  end.
Lemma SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F1F2 : forall x : SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Type, (SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F1 x <= 1) /\ SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F2 (SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F1 (SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_SyncConfigList_r16.

Opaque SL_SyncConfigList_r16__cond SL_SyncConfigList_r16__Format.

Record SL_FreqConfigCommon_r16__Type : Set :=
  make__SL_FreqConfigCommon_r16__Type {
    SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16 : SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__Type ;
    SL_FreqConfigCommon_r16__sl_AbsoluteFrequencyPointA_r16 : ARFCN_ValueNR__Type ;
    SL_FreqConfigCommon_r16__sl_AbsoluteFrequencySSB_r16 : option ARFCN_ValueNR__Type ;
    SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16 : option SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Type ;
    SL_FreqConfigCommon_r16__valueN_r16 : Z ;
    SL_FreqConfigCommon_r16__sl_BWP_List_r16 : option SL_FreqConfigCommon_r16__sl_BWP_List_r16__Type ;
    SL_FreqConfigCommon_r16__sl_SyncPriority_r16 : option SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Type ;
    SL_FreqConfigCommon_r16__sl_NbAsSync_r16 : option bool ;
    SL_FreqConfigCommon_r16__sl_SyncConfigList_r16 : option SL_SyncConfigList_r16__Type ;
}.
Definition SL_FreqConfigCommon_r16__root_list : list seq_elem := (
 Nor SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__Type SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__cond ::
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Type SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__cond ::
 Nor Z SL_FreqConfigCommon_r16__valueN_r16__cond ::
 Opt SL_FreqConfigCommon_r16__sl_BWP_List_r16__Type SL_FreqConfigCommon_r16__sl_BWP_List_r16__cond ::
 Opt SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Type SL_FreqConfigCommon_r16__sl_SyncPriority_r16__cond ::
 Opt bool (fun _ => True) ::
 Opt SL_SyncConfigList_r16__Type SL_SyncConfigList_r16__cond ::
 nil).
Definition SL_FreqConfigCommon_r16__ext_list : list typ := (
  nil).
Definition SL_FreqConfigCommon_r16__cond (z : SL_FreqConfigCommon_r16__Type) := 
(  SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__cond (SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16 z) /\
  ARFCN_ValueNR__cond (SL_FreqConfigCommon_r16__sl_AbsoluteFrequencyPointA_r16 z) /\
  opt_cond ARFCN_ValueNR__cond (SL_FreqConfigCommon_r16__sl_AbsoluteFrequencySSB_r16 z) /\
  opt_cond SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__cond (SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16 z) /\
  SL_FreqConfigCommon_r16__valueN_r16__cond (SL_FreqConfigCommon_r16__valueN_r16 z) /\
  opt_cond SL_FreqConfigCommon_r16__sl_BWP_List_r16__cond (SL_FreqConfigCommon_r16__sl_BWP_List_r16 z) /\
  opt_cond SL_FreqConfigCommon_r16__sl_SyncPriority_r16__cond (SL_FreqConfigCommon_r16__sl_SyncPriority_r16 z) /\
  opt_cond (fun _ => True) (SL_FreqConfigCommon_r16__sl_NbAsSync_r16 z) /\
  opt_cond SL_SyncConfigList_r16__cond (SL_FreqConfigCommon_r16__sl_SyncConfigList_r16 z) /\
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
Definition SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__Format : T_Format SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__Type SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__cond := seq_of_format SCS_SpecificCarrier__Format 1 maxSCSs SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__helper1 SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__helper2.

Opaque SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__cond SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__Format.

Definition SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Format : T_Format SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__nat__Format SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F1 SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F2 SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F1F2 SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__F2F1.

Opaque SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__cond SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Format.

Definition SL_FreqConfigCommon_r16__valueN_r16__Format : T_Format Z SL_FreqConfigCommon_r16__valueN_r16__cond :=
 ranged_int_format (-1) (1) SL_FreqConfigCommon_r16__valueN_r16__helper1 SL_FreqConfigCommon_r16__valueN_r16__helper2.

Opaque SL_FreqConfigCommon_r16__valueN_r16__cond SL_FreqConfigCommon_r16__valueN_r16__Format.

Definition SL_FreqConfigCommon_r16__sl_BWP_List_r16__Format : T_Format SL_FreqConfigCommon_r16__sl_BWP_List_r16__Type SL_FreqConfigCommon_r16__sl_BWP_List_r16__cond := seq_of_format SL_BWP_ConfigCommon_r16__Format 1 maxNrofSL_BWPs_r16 SL_FreqConfigCommon_r16__sl_BWP_List_r16__helper1 SL_FreqConfigCommon_r16__sl_BWP_List_r16__helper2.

Opaque SL_FreqConfigCommon_r16__sl_BWP_List_r16__cond SL_FreqConfigCommon_r16__sl_BWP_List_r16__Format.

Definition SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Format : T_Format SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_FreqConfigCommon_r16__sl_SyncPriority_r16__nat__Format SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F1 SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F2 SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F1F2 SL_FreqConfigCommon_r16__sl_SyncPriority_r16__F2F1.

Opaque SL_FreqConfigCommon_r16__sl_SyncPriority_r16__cond SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Format.


Definition SL_FreqConfigCommon_r16__root_Format_Type := Eval cbn in seq_format_prod SL_FreqConfigCommon_r16__root_list.
Definition SL_FreqConfigCommon_r16__root_Format_list : SL_FreqConfigCommon_r16__root_Format_Type :=
  (SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16__Format, (ARFCN_ValueNR__Format, (ARFCN_ValueNR__Format, (SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16__Format, (SL_FreqConfigCommon_r16__valueN_r16__Format, (SL_FreqConfigCommon_r16__sl_BWP_List_r16__Format, (SL_FreqConfigCommon_r16__sl_SyncPriority_r16__Format, (bool__Format, (SL_SyncConfigList_r16__Format, unit_format))))))))).

Definition SL_FreqConfigCommon_r16__ext_Format_Type := Eval cbn in get_formats SL_FreqConfigCommon_r16__ext_list.
Definition SL_FreqConfigCommon_r16__ext_Format_list : SL_FreqConfigCommon_r16__ext_Format_Type :=
  unit__Format.

Definition SL_FreqConfigCommon_r16__list_type : Set := (seq_type SL_FreqConfigCommon_r16__root_list) * (seq_ext_type SL_FreqConfigCommon_r16__ext_list).
Definition SL_FreqConfigCommon_r16__list_cond (z : SL_FreqConfigCommon_r16__list_type) : Prop :=
        (seq_cond SL_FreqConfigCommon_r16__root_list (fst z)) /\ (seq_ext_cond SL_FreqConfigCommon_r16__ext_list (snd z)).
Definition SL_FreqConfigCommon_r16__list_format : T_Format SL_FreqConfigCommon_r16__list_type SL_FreqConfigCommon_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_FreqConfigCommon_r16__root_list SL_FreqConfigCommon_r16__root_Format_list SL_FreqConfigCommon_r16__ext_list SL_FreqConfigCommon_r16__ext_Format_list.

Opaque SL_FreqConfigCommon_r16__list_format.
Definition SL_FreqConfigCommon_r16__F1 (z : SL_FreqConfigCommon_r16__Type) : SL_FreqConfigCommon_r16__list_type :=
  (((SL_FreqConfigCommon_r16__sl_SCS_SpecificCarrierList_r16 z, (SL_FreqConfigCommon_r16__sl_AbsoluteFrequencyPointA_r16 z, (SL_FreqConfigCommon_r16__sl_AbsoluteFrequencySSB_r16 z, (SL_FreqConfigCommon_r16__frequencyShift7p5khzSL_r16 z, (SL_FreqConfigCommon_r16__valueN_r16 z, (SL_FreqConfigCommon_r16__sl_BWP_List_r16 z, (SL_FreqConfigCommon_r16__sl_SyncPriority_r16 z, (SL_FreqConfigCommon_r16__sl_NbAsSync_r16 z, (SL_FreqConfigCommon_r16__sl_SyncConfigList_r16 z, tt)))))))))), (
tt)).
Definition SL_FreqConfigCommon_r16__F2 (y : SL_FreqConfigCommon_r16__list_type) : SL_FreqConfigCommon_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), _)=>
    make__SL_FreqConfigCommon_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8
  end.
Definition SL_FreqConfigCommon_r16__helper1 : (forall a : SL_FreqConfigCommon_r16__Type, SL_FreqConfigCommon_r16__cond a -> SL_FreqConfigCommon_r16__list_cond (SL_FreqConfigCommon_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_FreqConfigCommon_r16__helper2 : (forall a : SL_FreqConfigCommon_r16__Type, SL_FreqConfigCommon_r16__F2 (SL_FreqConfigCommon_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_FreqConfigCommon_r16__helper3 : (forall b : SL_FreqConfigCommon_r16__list_type, SL_FreqConfigCommon_r16__list_cond b -> SL_FreqConfigCommon_r16__cond (SL_FreqConfigCommon_r16__F2 b) /\ SL_FreqConfigCommon_r16__F1 (SL_FreqConfigCommon_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_FreqConfigCommon_r16__cond, SL_FreqConfigCommon_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_FreqConfigCommon_r16__Format : T_Format SL_FreqConfigCommon_r16__Type SL_FreqConfigCommon_r16__cond :=
 proj2_format SL_FreqConfigCommon_r16__cond SL_FreqConfigCommon_r16__list_format  SL_FreqConfigCommon_r16__F1 SL_FreqConfigCommon_r16__F2 SL_FreqConfigCommon_r16__helper1 SL_FreqConfigCommon_r16__helper2 SL_FreqConfigCommon_r16__helper3.

Opaque SL_FreqConfigCommon_r16__cond SL_FreqConfigCommon_r16__Format.

