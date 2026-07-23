Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PosSchedulingInfo_r16.

Opaque PosSchedulingInfo_r16__cond PosSchedulingInfo_r16__Format.

Definition PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__Type := list PosSchedulingInfo_r16__Type.

Lemma PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__helper1 : (0 <= 1 <= maxSI_Message)%Z. unfold maxSI_Message.
 lia. Qed.
Lemma PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__helper2 : to_bit_sz (Z.to_nat (maxSI_Message - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSI_Message - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__cond (z : PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSI_Message)%Z /\ (list_and PosSchedulingInfo_r16__cond z) .

Require Import NR.SI_RequestConfig.

Opaque SI_RequestConfig__cond SI_RequestConfig__Format.

Require Import NR.SI_RequestConfig.

Opaque SI_RequestConfig__cond SI_RequestConfig__Format.

Require Import NR.SI_RequestConfig.

Opaque SI_RequestConfig__cond SI_RequestConfig__Format.

Record PosSI_SchedulingInfo_r16__ext0O__Type : Set :=
  make__PosSI_SchedulingInfo_r16__ext0O__Type {
    PosSI_SchedulingInfo_r16__ext0O__posSI_RequestConfigRedCap_r17 : option SI_RequestConfig__Type ;
}.
Definition PosSI_SchedulingInfo_r16__ext0O__list := (
 Opt SI_RequestConfig__Type SI_RequestConfig__cond ::
 nil).
Definition PosSI_SchedulingInfo_r16__ext0O__cond z := 
  opt_cond SI_RequestConfig__cond (PosSI_SchedulingInfo_r16__ext0O__posSI_RequestConfigRedCap_r17 z) /\
  True.

Definition PosSI_SchedulingInfo_r16__ext0__Type := PosSI_SchedulingInfo_r16__ext0O__Type.
Definition PosSI_SchedulingInfo_r16__ext0__cond := PosSI_SchedulingInfo_r16__ext0O__cond.

Record PosSI_SchedulingInfo_r16__Type : Set :=
  make__PosSI_SchedulingInfo_r16__Type {
    PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16 : PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__Type ;
    PosSI_SchedulingInfo_r16__posSI_RequestConfig_r16 : option SI_RequestConfig__Type ;
    PosSI_SchedulingInfo_r16__posSI_RequestConfigSUL_r16 : option SI_RequestConfig__Type ;
    PosSI_SchedulingInfo_r16__ext0 : option PosSI_SchedulingInfo_r16__ext0__Type ;
}.
Definition PosSI_SchedulingInfo_r16__root_list : list seq_elem := (
 Nor PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__Type PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__cond ::
 Opt SI_RequestConfig__Type SI_RequestConfig__cond ::
 Opt SI_RequestConfig__Type SI_RequestConfig__cond ::
 nil).
Definition PosSI_SchedulingInfo_r16__ext_list : list typ := (
  typ_cons PosSI_SchedulingInfo_r16__ext0__Type PosSI_SchedulingInfo_r16__ext0__cond ::
  nil).
Definition PosSI_SchedulingInfo_r16__cond (z : PosSI_SchedulingInfo_r16__Type) := 
(  PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__cond (PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16 z) /\
  opt_cond SI_RequestConfig__cond (PosSI_SchedulingInfo_r16__posSI_RequestConfig_r16 z) /\
  opt_cond SI_RequestConfig__cond (PosSI_SchedulingInfo_r16__posSI_RequestConfigSUL_r16 z) /\
  True) /\ 
(  opt_cond PosSI_SchedulingInfo_r16__ext0__cond (PosSI_SchedulingInfo_r16__ext0 z) /\
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
Definition PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__Format : T_Format PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__Type PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__cond := seq_of_format PosSchedulingInfo_r16__Format 1 maxSI_Message PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__helper1 PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__helper2.

Opaque PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__cond PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__Format.


Definition PosSI_SchedulingInfo_r16__ext0O__Format_Type := Eval cbn in seq_format_prod PosSI_SchedulingInfo_r16__ext0O__list.
Definition PosSI_SchedulingInfo_r16__ext0O__Format_list : PosSI_SchedulingInfo_r16__ext0O__Format_Type :=
  (SI_RequestConfig__Format, unit_format).
Definition PosSI_SchedulingInfo_r16__ext0O__list__Format := (*Eval compute in *) seq_format PosSI_SchedulingInfo_r16__ext0O__list PosSI_SchedulingInfo_r16__ext0O__Format_list.
Definition PosSI_SchedulingInfo_r16__ext0O__F1 z :=
  (PosSI_SchedulingInfo_r16__ext0O__posSI_RequestConfigRedCap_r17 z, tt).
Definition PosSI_SchedulingInfo_r16__ext0O__F2 (y : seq_type PosSI_SchedulingInfo_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PosSI_SchedulingInfo_r16__ext0O__Type i0
  end.
Lemma PosSI_SchedulingInfo_r16__ext0O__F1F2_cond (z : PosSI_SchedulingInfo_r16__ext0O__Type)
  : PosSI_SchedulingInfo_r16__ext0O__cond z ->
  (seq_cond PosSI_SchedulingInfo_r16__ext0O__list (PosSI_SchedulingInfo_r16__ext0O__F1 z)).
intro H. unfold PosSI_SchedulingInfo_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma PosSI_SchedulingInfo_r16__ext0O__F1F2_cond2 (z : PosSI_SchedulingInfo_r16__ext0O__Type)
 : PosSI_SchedulingInfo_r16__ext0O__F2 (PosSI_SchedulingInfo_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PosSI_SchedulingInfo_r16__ext0O__F2F1_cond (y : seq_type PosSI_SchedulingInfo_r16__ext0O__list)
  : seq_cond PosSI_SchedulingInfo_r16__ext0O__list y ->
 (PosSI_SchedulingInfo_r16__ext0O__cond (PosSI_SchedulingInfo_r16__ext0O__F2 y)) /\  PosSI_SchedulingInfo_r16__ext0O__F1 (PosSI_SchedulingInfo_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PosSI_SchedulingInfo_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold PosSI_SchedulingInfo_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PosSI_SchedulingInfo_r16__ext0O__Format : T_Format PosSI_SchedulingInfo_r16__ext0O__Type PosSI_SchedulingInfo_r16__ext0O__cond :=
        proj2_format  PosSI_SchedulingInfo_r16__ext0O__cond PosSI_SchedulingInfo_r16__ext0O__list__Format
    PosSI_SchedulingInfo_r16__ext0O__F1 PosSI_SchedulingInfo_r16__ext0O__F2 PosSI_SchedulingInfo_r16__ext0O__F1F2_cond  PosSI_SchedulingInfo_r16__ext0O__F1F2_cond2 PosSI_SchedulingInfo_r16__ext0O__F2F1_cond.
Opaque PosSI_SchedulingInfo_r16__ext0O__cond PosSI_SchedulingInfo_r16__ext0O__Format.

Definition PosSI_SchedulingInfo_r16__ext0__check_all_none (b : PosSI_SchedulingInfo_r16__ext0O__Type) : bool :=
match b with 
  | make__PosSI_SchedulingInfo_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PosSI_SchedulingInfo_r16__ext0__Format : T_Format PosSI_SchedulingInfo_r16__ext0__Type PosSI_SchedulingInfo_r16__ext0__cond :=
  restrict_add_format PosSI_SchedulingInfo_r16__ext0__check_all_none PosSI_SchedulingInfo_r16__ext0O__Format.

Opaque PosSI_SchedulingInfo_r16__ext0__cond PosSI_SchedulingInfo_r16__ext0__Format.


Definition PosSI_SchedulingInfo_r16__root_Format_Type := Eval cbn in seq_format_prod PosSI_SchedulingInfo_r16__root_list.
Definition PosSI_SchedulingInfo_r16__root_Format_list : PosSI_SchedulingInfo_r16__root_Format_Type :=
  (PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16__Format, (SI_RequestConfig__Format, (SI_RequestConfig__Format, unit_format))).

Definition PosSI_SchedulingInfo_r16__ext_Format_Type := Eval cbn in get_formats PosSI_SchedulingInfo_r16__ext_list.
Definition PosSI_SchedulingInfo_r16__ext_Format_list : PosSI_SchedulingInfo_r16__ext_Format_Type :=
  (PosSI_SchedulingInfo_r16__ext0__Format, unit__Format).

Definition PosSI_SchedulingInfo_r16__list_type : Set := (seq_type PosSI_SchedulingInfo_r16__root_list) * (seq_ext_type PosSI_SchedulingInfo_r16__ext_list).
Definition PosSI_SchedulingInfo_r16__list_cond (z : PosSI_SchedulingInfo_r16__list_type) : Prop :=
        (seq_cond PosSI_SchedulingInfo_r16__root_list (fst z)) /\ (seq_ext_cond PosSI_SchedulingInfo_r16__ext_list (snd z)).
Definition PosSI_SchedulingInfo_r16__list_format : T_Format PosSI_SchedulingInfo_r16__list_type PosSI_SchedulingInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format PosSI_SchedulingInfo_r16__root_list PosSI_SchedulingInfo_r16__root_Format_list PosSI_SchedulingInfo_r16__ext_list PosSI_SchedulingInfo_r16__ext_Format_list.

Opaque PosSI_SchedulingInfo_r16__list_format.
Definition PosSI_SchedulingInfo_r16__F1 (z : PosSI_SchedulingInfo_r16__Type) : PosSI_SchedulingInfo_r16__list_type :=
  (((PosSI_SchedulingInfo_r16__posSchedulingInfoList_r16 z, (PosSI_SchedulingInfo_r16__posSI_RequestConfig_r16 z, (PosSI_SchedulingInfo_r16__posSI_RequestConfigSUL_r16 z, tt)))), (
(PosSI_SchedulingInfo_r16__ext0 z, tt))).
Definition PosSI_SchedulingInfo_r16__F2 (y : PosSI_SchedulingInfo_r16__list_type) : PosSI_SchedulingInfo_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__PosSI_SchedulingInfo_r16__Type j0 j1 j2 i0
  end.
Definition PosSI_SchedulingInfo_r16__helper1 : (forall a : PosSI_SchedulingInfo_r16__Type, PosSI_SchedulingInfo_r16__cond a -> PosSI_SchedulingInfo_r16__list_cond (PosSI_SchedulingInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PosSI_SchedulingInfo_r16__helper2 : (forall a : PosSI_SchedulingInfo_r16__Type, PosSI_SchedulingInfo_r16__F2 (PosSI_SchedulingInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PosSI_SchedulingInfo_r16__helper3 : (forall b : PosSI_SchedulingInfo_r16__list_type, PosSI_SchedulingInfo_r16__list_cond b -> PosSI_SchedulingInfo_r16__cond (PosSI_SchedulingInfo_r16__F2 b) /\ PosSI_SchedulingInfo_r16__F1 (PosSI_SchedulingInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PosSI_SchedulingInfo_r16__cond, PosSI_SchedulingInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PosSI_SchedulingInfo_r16__Format : T_Format PosSI_SchedulingInfo_r16__Type PosSI_SchedulingInfo_r16__cond :=
 proj2_format PosSI_SchedulingInfo_r16__cond PosSI_SchedulingInfo_r16__list_format  PosSI_SchedulingInfo_r16__F1 PosSI_SchedulingInfo_r16__F2 PosSI_SchedulingInfo_r16__helper1 PosSI_SchedulingInfo_r16__helper2 PosSI_SchedulingInfo_r16__helper3.

Opaque PosSI_SchedulingInfo_r16__cond PosSI_SchedulingInfo_r16__Format.

