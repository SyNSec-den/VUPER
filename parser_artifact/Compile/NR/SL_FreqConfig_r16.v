Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_Freq_Id_r16.

Opaque SL_Freq_Id_r16__cond SL_Freq_Id_r16__Format.

Require Import NR.SCS_SpecificCarrier.

Opaque SCS_SpecificCarrier__cond SCS_SpecificCarrier__Format.

Definition SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__Type := list SCS_SpecificCarrier__Type.

Lemma SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__cond (z : SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SCS_SpecificCarrier__cond z) .

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Inductive SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Type : Set :=
 | SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__true
.
Definition SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__cond := (fun (_ : SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Type) => True).
Lemma SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__nat__helper.

Definition SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F1 t :=
  match t with
  | SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__true => 0
  end.
Definition SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F2 n :=
  match n with
  | 0 => SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__true
  | _ => SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__true
  end.
Lemma SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F1F2 : forall x : SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Type, (SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F1 x <= 0) /\ SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F2 (SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F1 (SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_FreqConfig_r16__valueN_r16__helper1 : (-1 <= 1)%Z.  lia. Qed.
Lemma SL_FreqConfig_r16__valueN_r16__helper2 : to_bit_sz (Z.to_nat (1 - -1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - -1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_FreqConfig_r16__valueN_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_FreqConfig_r16__valueN_r16__Type := Z.
Definition SL_FreqConfig_r16__valueN_r16__cond := (fun z => (-1 <= z <= 1)%Z).
Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Definition SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__Type := list BWP_Id__Type.

Lemma SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofSL_BWPs_r16)%Z. unfold maxNrofSL_BWPs_r16.
 lia. Qed.
Lemma SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_BWPs_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_BWPs_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__cond (z : SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_BWPs_r16)%Z /\ (list_and BWP_Id__cond z) .

Require Import NR.SL_BWP_Config_r16.

Opaque SL_BWP_Config_r16__cond SL_BWP_Config_r16__Format.

Definition SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__Type := list SL_BWP_Config_r16__Type.

Lemma SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__helper1 : (0 <= 1 <= maxNrofSL_BWPs_r16)%Z. unfold maxNrofSL_BWPs_r16.
 lia. Qed.
Lemma SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_BWPs_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_BWPs_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__cond (z : SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_BWPs_r16)%Z /\ (list_and SL_BWP_Config_r16__cond z) .

Require Import NR.SL_SyncConfigList_r16.

Opaque SL_SyncConfigList_r16__cond SL_SyncConfigList_r16__Format.

Inductive SL_FreqConfig_r16__sl_SyncPriority_r16__Type : Set :=
 | SL_FreqConfig_r16__sl_SyncPriority_r16__gnss
 | SL_FreqConfig_r16__sl_SyncPriority_r16__gnbEnb
.
Definition SL_FreqConfig_r16__sl_SyncPriority_r16__cond := (fun (_ : SL_FreqConfig_r16__sl_SyncPriority_r16__Type) => True).
Lemma SL_FreqConfig_r16__sl_SyncPriority_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_FreqConfig_r16__sl_SyncPriority_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_FreqConfig_r16__sl_SyncPriority_r16__nat__helper.

Definition SL_FreqConfig_r16__sl_SyncPriority_r16__F1 t :=
  match t with
  | SL_FreqConfig_r16__sl_SyncPriority_r16__gnss => 0
  | SL_FreqConfig_r16__sl_SyncPriority_r16__gnbEnb => 1
  end.
Definition SL_FreqConfig_r16__sl_SyncPriority_r16__F2 n :=
  match n with
  | 0 => SL_FreqConfig_r16__sl_SyncPriority_r16__gnss
  | 1 => SL_FreqConfig_r16__sl_SyncPriority_r16__gnbEnb
  | _ => SL_FreqConfig_r16__sl_SyncPriority_r16__gnss
  end.
Lemma SL_FreqConfig_r16__sl_SyncPriority_r16__F1F2 : forall x : SL_FreqConfig_r16__sl_SyncPriority_r16__Type, (SL_FreqConfig_r16__sl_SyncPriority_r16__F1 x <= 1) /\ SL_FreqConfig_r16__sl_SyncPriority_r16__F2 (SL_FreqConfig_r16__sl_SyncPriority_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_FreqConfig_r16__sl_SyncPriority_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_FreqConfig_r16__sl_SyncPriority_r16__F1 (SL_FreqConfig_r16__sl_SyncPriority_r16__F2 y) = y. enum_solve H y. Qed.

Record SL_FreqConfig_r16__Type : Set :=
  make__SL_FreqConfig_r16__Type {
    SL_FreqConfig_r16__sl_Freq_Id_r16 : SL_Freq_Id_r16__Type ;
    SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16 : SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__Type ;
    SL_FreqConfig_r16__sl_AbsoluteFrequencyPointA_r16 : option ARFCN_ValueNR__Type ;
    SL_FreqConfig_r16__sl_AbsoluteFrequencySSB_r16 : option ARFCN_ValueNR__Type ;
    SL_FreqConfig_r16__frequencyShift7p5khzSL_r16 : option SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Type ;
    SL_FreqConfig_r16__valueN_r16 : Z ;
    SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16 : option SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__Type ;
    SL_FreqConfig_r16__sl_BWP_ToAddModList_r16 : option SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__Type ;
    SL_FreqConfig_r16__sl_SyncConfigList_r16 : option SL_SyncConfigList_r16__Type ;
    SL_FreqConfig_r16__sl_SyncPriority_r16 : option SL_FreqConfig_r16__sl_SyncPriority_r16__Type ;
}.
Definition SL_FreqConfig_r16__list := (
 Nor SL_Freq_Id_r16__Type SL_Freq_Id_r16__cond ::
 Nor SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__Type SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__cond ::
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Type SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__cond ::
 Nor Z SL_FreqConfig_r16__valueN_r16__cond ::
 Opt SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__Type SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__cond ::
 Opt SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__Type SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__cond ::
 Opt SL_SyncConfigList_r16__Type SL_SyncConfigList_r16__cond ::
 Opt SL_FreqConfig_r16__sl_SyncPriority_r16__Type SL_FreqConfig_r16__sl_SyncPriority_r16__cond ::
 nil).
Definition SL_FreqConfig_r16__cond z := 
  SL_Freq_Id_r16__cond (SL_FreqConfig_r16__sl_Freq_Id_r16 z) /\
  SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__cond (SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16 z) /\
  opt_cond ARFCN_ValueNR__cond (SL_FreqConfig_r16__sl_AbsoluteFrequencyPointA_r16 z) /\
  opt_cond ARFCN_ValueNR__cond (SL_FreqConfig_r16__sl_AbsoluteFrequencySSB_r16 z) /\
  opt_cond SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__cond (SL_FreqConfig_r16__frequencyShift7p5khzSL_r16 z) /\
  SL_FreqConfig_r16__valueN_r16__cond (SL_FreqConfig_r16__valueN_r16 z) /\
  opt_cond SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__cond (SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16 z) /\
  opt_cond SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__cond (SL_FreqConfig_r16__sl_BWP_ToAddModList_r16 z) /\
  opt_cond SL_SyncConfigList_r16__cond (SL_FreqConfig_r16__sl_SyncConfigList_r16 z) /\
  opt_cond SL_FreqConfig_r16__sl_SyncPriority_r16__cond (SL_FreqConfig_r16__sl_SyncPriority_r16 z) /\
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
Definition SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__Format : T_Format SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__Type SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__cond := seq_of_format SCS_SpecificCarrier__Format 1 maxSCSs SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__helper1 SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__helper2.

Opaque SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__cond SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__Format.

Definition SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Format : T_Format SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__nat__Format SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F1 SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F2 SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F1F2 SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__F2F1.

Opaque SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__cond SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Format.

Definition SL_FreqConfig_r16__valueN_r16__Format : T_Format Z SL_FreqConfig_r16__valueN_r16__cond :=
 ranged_int_format (-1) (1) SL_FreqConfig_r16__valueN_r16__helper1 SL_FreqConfig_r16__valueN_r16__helper2.

Opaque SL_FreqConfig_r16__valueN_r16__cond SL_FreqConfig_r16__valueN_r16__Format.

Definition SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__Format : T_Format SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__Type SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__cond := seq_of_format BWP_Id__Format 1 maxNrofSL_BWPs_r16 SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__helper1 SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__helper2.

Opaque SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__cond SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__Format.

Definition SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__Format : T_Format SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__Type SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__cond := seq_of_format SL_BWP_Config_r16__Format 1 maxNrofSL_BWPs_r16 SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__helper1 SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__helper2.

Opaque SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__cond SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__Format.

Definition SL_FreqConfig_r16__sl_SyncPriority_r16__Format : T_Format SL_FreqConfig_r16__sl_SyncPriority_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_FreqConfig_r16__sl_SyncPriority_r16__nat__Format SL_FreqConfig_r16__sl_SyncPriority_r16__F1 SL_FreqConfig_r16__sl_SyncPriority_r16__F2 SL_FreqConfig_r16__sl_SyncPriority_r16__F1F2 SL_FreqConfig_r16__sl_SyncPriority_r16__F2F1.

Opaque SL_FreqConfig_r16__sl_SyncPriority_r16__cond SL_FreqConfig_r16__sl_SyncPriority_r16__Format.


Definition SL_FreqConfig_r16__Format_Type := Eval cbn in seq_format_prod SL_FreqConfig_r16__list.
Definition SL_FreqConfig_r16__Format_list : SL_FreqConfig_r16__Format_Type :=
  (SL_Freq_Id_r16__Format, (SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16__Format, (ARFCN_ValueNR__Format, (ARFCN_ValueNR__Format, (SL_FreqConfig_r16__frequencyShift7p5khzSL_r16__Format, (SL_FreqConfig_r16__valueN_r16__Format, (SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16__Format, (SL_FreqConfig_r16__sl_BWP_ToAddModList_r16__Format, (SL_SyncConfigList_r16__Format, (SL_FreqConfig_r16__sl_SyncPriority_r16__Format, unit_format)))))))))).
Definition SL_FreqConfig_r16__list__Format := (*Eval compute in *) seq_format SL_FreqConfig_r16__list SL_FreqConfig_r16__Format_list.
Definition SL_FreqConfig_r16__F1 z :=
  (SL_FreqConfig_r16__sl_Freq_Id_r16 z, (SL_FreqConfig_r16__sl_SCS_SpecificCarrierList_r16 z, (SL_FreqConfig_r16__sl_AbsoluteFrequencyPointA_r16 z, (SL_FreqConfig_r16__sl_AbsoluteFrequencySSB_r16 z, (SL_FreqConfig_r16__frequencyShift7p5khzSL_r16 z, (SL_FreqConfig_r16__valueN_r16 z, (SL_FreqConfig_r16__sl_BWP_ToReleaseList_r16 z, (SL_FreqConfig_r16__sl_BWP_ToAddModList_r16 z, (SL_FreqConfig_r16__sl_SyncConfigList_r16 z, (SL_FreqConfig_r16__sl_SyncPriority_r16 z, tt)))))))))).
Definition SL_FreqConfig_r16__F2 (y : seq_type SL_FreqConfig_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__SL_FreqConfig_r16__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma SL_FreqConfig_r16__F1F2_cond (z : SL_FreqConfig_r16__Type)
  : SL_FreqConfig_r16__cond z ->
  (seq_cond SL_FreqConfig_r16__list (SL_FreqConfig_r16__F1 z)).
intro H. unfold SL_FreqConfig_r16__cond in H. simpl. auto. Qed.
Lemma SL_FreqConfig_r16__F1F2_cond2 (z : SL_FreqConfig_r16__Type)
 : SL_FreqConfig_r16__F2 (SL_FreqConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_FreqConfig_r16__F2F1_cond (y : seq_type SL_FreqConfig_r16__list)
  : seq_cond SL_FreqConfig_r16__list y ->
 (SL_FreqConfig_r16__cond (SL_FreqConfig_r16__F2 y)) /\  SL_FreqConfig_r16__F1 (SL_FreqConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_FreqConfig_r16__cond. simpl in *. auto.
 - simpl. unfold SL_FreqConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_FreqConfig_r16__Format : T_Format SL_FreqConfig_r16__Type SL_FreqConfig_r16__cond :=
        proj2_format  SL_FreqConfig_r16__cond SL_FreqConfig_r16__list__Format
    SL_FreqConfig_r16__F1 SL_FreqConfig_r16__F2 SL_FreqConfig_r16__F1F2_cond  SL_FreqConfig_r16__F1F2_cond2 SL_FreqConfig_r16__F2F1_cond.
Opaque SL_FreqConfig_r16__cond SL_FreqConfig_r16__Format.

