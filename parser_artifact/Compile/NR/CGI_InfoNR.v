Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_IdentityInfoList.

Opaque PLMN_IdentityInfoList__cond PLMN_IdentityInfoList__Format.

Require Import NR.MultiFrequencyBandListNR.

Opaque MultiFrequencyBandListNR__cond MultiFrequencyBandListNR__Format.

Lemma CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__Type := Z.
Definition CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__cond := (fun z => (0 <= z <= 15)%Z).
Require Import NR.PDCCH_ConfigSIB1.

Opaque PDCCH_ConfigSIB1__cond PDCCH_ConfigSIB1__Format.

Record CGI_InfoNR__noSIB1__Type : Set :=
  make__CGI_InfoNR__noSIB1__Type {
    CGI_InfoNR__noSIB1__ssb_SubcarrierOffset : Z ;
    CGI_InfoNR__noSIB1__pdcch_ConfigSIB1 : PDCCH_ConfigSIB1__Type ;
}.
Definition CGI_InfoNR__noSIB1__list := (
 Nor Z CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__cond ::
 Nor PDCCH_ConfigSIB1__Type PDCCH_ConfigSIB1__cond ::
 nil).
Definition CGI_InfoNR__noSIB1__cond z := 
  CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__cond (CGI_InfoNR__noSIB1__ssb_SubcarrierOffset z) /\
  PDCCH_ConfigSIB1__cond (CGI_InfoNR__noSIB1__pdcch_ConfigSIB1 z) /\
  True.

Require Import NR.NPN_IdentityInfoList_r16.

Opaque NPN_IdentityInfoList_r16__cond NPN_IdentityInfoList_r16__Format.

Record CGI_InfoNR__ext0O__Type : Set :=
  make__CGI_InfoNR__ext0O__Type {
    CGI_InfoNR__ext0O__npn_IdentityInfoList_r16 : option NPN_IdentityInfoList_r16__Type ;
}.
Definition CGI_InfoNR__ext0O__list := (
 Opt NPN_IdentityInfoList_r16__Type NPN_IdentityInfoList_r16__cond ::
 nil).
Definition CGI_InfoNR__ext0O__cond z := 
  opt_cond NPN_IdentityInfoList_r16__cond (CGI_InfoNR__ext0O__npn_IdentityInfoList_r16 z) /\
  True.

Definition CGI_InfoNR__ext0__Type := CGI_InfoNR__ext0O__Type.
Definition CGI_InfoNR__ext0__cond := CGI_InfoNR__ext0O__cond.

Inductive CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type : Set :=
 | CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__true
.
Definition CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__cond := (fun (_ : CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type) => True).
Lemma CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__nat__helper.

Definition CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F1 t :=
  match t with
  | CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__true => 0
  end.
Definition CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F2 n :=
  match n with
  | 0 => CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__true
  | _ => CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__true
  end.
Lemma CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F1F2 : forall x : CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type, (CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F1 x <= 0) /\ CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F2 (CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F1 x) = x. imp_solve. Qed.
Lemma CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F2F1 : forall (y : nat) (H : y <= 0), CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F1 (CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F2 y) = y. enum_solve H y. Qed.

Record CGI_InfoNR__ext1O__Type : Set :=
  make__CGI_InfoNR__ext1O__Type {
    CGI_InfoNR__ext1O__cellReservedForOtherUse_r16 : option CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type ;
}.
Definition CGI_InfoNR__ext1O__list := (
 Opt CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__cond ::
 nil).
Definition CGI_InfoNR__ext1O__cond z := 
  opt_cond CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__cond (CGI_InfoNR__ext1O__cellReservedForOtherUse_r16 z) /\
  True.

Definition CGI_InfoNR__ext1__Type := CGI_InfoNR__ext1O__Type.
Definition CGI_InfoNR__ext1__cond := CGI_InfoNR__ext1O__cond.

Record CGI_InfoNR__Type : Set :=
  make__CGI_InfoNR__Type {
    CGI_InfoNR__plmn_IdentityInfoList : option PLMN_IdentityInfoList__Type ;
    CGI_InfoNR__frequencyBandList : option MultiFrequencyBandListNR__Type ;
    CGI_InfoNR__noSIB1 : option CGI_InfoNR__noSIB1__Type ;
    CGI_InfoNR__ext0 : option CGI_InfoNR__ext0__Type ;
    CGI_InfoNR__ext1 : option CGI_InfoNR__ext1__Type ;
}.
Definition CGI_InfoNR__root_list : list seq_elem := (
 Opt PLMN_IdentityInfoList__Type PLMN_IdentityInfoList__cond ::
 Opt MultiFrequencyBandListNR__Type MultiFrequencyBandListNR__cond ::
 Opt CGI_InfoNR__noSIB1__Type CGI_InfoNR__noSIB1__cond ::
 nil).
Definition CGI_InfoNR__ext_list : list typ := (
  typ_cons CGI_InfoNR__ext0__Type CGI_InfoNR__ext0__cond ::
  typ_cons CGI_InfoNR__ext1__Type CGI_InfoNR__ext1__cond ::
  nil).
Definition CGI_InfoNR__cond (z : CGI_InfoNR__Type) := 
(  opt_cond PLMN_IdentityInfoList__cond (CGI_InfoNR__plmn_IdentityInfoList z) /\
  opt_cond MultiFrequencyBandListNR__cond (CGI_InfoNR__frequencyBandList z) /\
  opt_cond CGI_InfoNR__noSIB1__cond (CGI_InfoNR__noSIB1 z) /\
  True) /\ 
(  opt_cond CGI_InfoNR__ext0__cond (CGI_InfoNR__ext0 z) /\
  opt_cond CGI_InfoNR__ext1__cond (CGI_InfoNR__ext1 z) /\
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
Definition CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__Format : T_Format Z CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__cond :=
 ranged_int_format (0) (15) CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__helper1 CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__helper2.

Opaque CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__cond CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__Format.


Definition CGI_InfoNR__noSIB1__Format_Type := Eval cbn in seq_format_prod CGI_InfoNR__noSIB1__list.
Definition CGI_InfoNR__noSIB1__Format_list : CGI_InfoNR__noSIB1__Format_Type :=
  (CGI_InfoNR__noSIB1__ssb_SubcarrierOffset__Format, (PDCCH_ConfigSIB1__Format, unit_format)).
Definition CGI_InfoNR__noSIB1__list__Format := (*Eval compute in *) seq_format CGI_InfoNR__noSIB1__list CGI_InfoNR__noSIB1__Format_list.
Definition CGI_InfoNR__noSIB1__F1 z :=
  (CGI_InfoNR__noSIB1__ssb_SubcarrierOffset z, (CGI_InfoNR__noSIB1__pdcch_ConfigSIB1 z, tt)).
Definition CGI_InfoNR__noSIB1__F2 (y : seq_type CGI_InfoNR__noSIB1__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CGI_InfoNR__noSIB1__Type i0 i1
  end.
Lemma CGI_InfoNR__noSIB1__F1F2_cond (z : CGI_InfoNR__noSIB1__Type)
  : CGI_InfoNR__noSIB1__cond z ->
  (seq_cond CGI_InfoNR__noSIB1__list (CGI_InfoNR__noSIB1__F1 z)).
intro H. unfold CGI_InfoNR__noSIB1__cond in H. simpl. auto. Qed.
Lemma CGI_InfoNR__noSIB1__F1F2_cond2 (z : CGI_InfoNR__noSIB1__Type)
 : CGI_InfoNR__noSIB1__F2 (CGI_InfoNR__noSIB1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CGI_InfoNR__noSIB1__F2F1_cond (y : seq_type CGI_InfoNR__noSIB1__list)
  : seq_cond CGI_InfoNR__noSIB1__list y ->
 (CGI_InfoNR__noSIB1__cond (CGI_InfoNR__noSIB1__F2 y)) /\  CGI_InfoNR__noSIB1__F1 (CGI_InfoNR__noSIB1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CGI_InfoNR__noSIB1__cond. simpl in *. auto.
 - simpl. unfold CGI_InfoNR__noSIB1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CGI_InfoNR__noSIB1__Format : T_Format CGI_InfoNR__noSIB1__Type CGI_InfoNR__noSIB1__cond :=
        proj2_format  CGI_InfoNR__noSIB1__cond CGI_InfoNR__noSIB1__list__Format
    CGI_InfoNR__noSIB1__F1 CGI_InfoNR__noSIB1__F2 CGI_InfoNR__noSIB1__F1F2_cond  CGI_InfoNR__noSIB1__F1F2_cond2 CGI_InfoNR__noSIB1__F2F1_cond.
Opaque CGI_InfoNR__noSIB1__cond CGI_InfoNR__noSIB1__Format.


Definition CGI_InfoNR__ext0O__Format_Type := Eval cbn in seq_format_prod CGI_InfoNR__ext0O__list.
Definition CGI_InfoNR__ext0O__Format_list : CGI_InfoNR__ext0O__Format_Type :=
  (NPN_IdentityInfoList_r16__Format, unit_format).
Definition CGI_InfoNR__ext0O__list__Format := (*Eval compute in *) seq_format CGI_InfoNR__ext0O__list CGI_InfoNR__ext0O__Format_list.
Definition CGI_InfoNR__ext0O__F1 z :=
  (CGI_InfoNR__ext0O__npn_IdentityInfoList_r16 z, tt).
Definition CGI_InfoNR__ext0O__F2 (y : seq_type CGI_InfoNR__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CGI_InfoNR__ext0O__Type i0
  end.
Lemma CGI_InfoNR__ext0O__F1F2_cond (z : CGI_InfoNR__ext0O__Type)
  : CGI_InfoNR__ext0O__cond z ->
  (seq_cond CGI_InfoNR__ext0O__list (CGI_InfoNR__ext0O__F1 z)).
intro H. unfold CGI_InfoNR__ext0O__cond in H. simpl. auto. Qed.
Lemma CGI_InfoNR__ext0O__F1F2_cond2 (z : CGI_InfoNR__ext0O__Type)
 : CGI_InfoNR__ext0O__F2 (CGI_InfoNR__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CGI_InfoNR__ext0O__F2F1_cond (y : seq_type CGI_InfoNR__ext0O__list)
  : seq_cond CGI_InfoNR__ext0O__list y ->
 (CGI_InfoNR__ext0O__cond (CGI_InfoNR__ext0O__F2 y)) /\  CGI_InfoNR__ext0O__F1 (CGI_InfoNR__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CGI_InfoNR__ext0O__cond. simpl in *. auto.
 - simpl. unfold CGI_InfoNR__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CGI_InfoNR__ext0O__Format : T_Format CGI_InfoNR__ext0O__Type CGI_InfoNR__ext0O__cond :=
        proj2_format  CGI_InfoNR__ext0O__cond CGI_InfoNR__ext0O__list__Format
    CGI_InfoNR__ext0O__F1 CGI_InfoNR__ext0O__F2 CGI_InfoNR__ext0O__F1F2_cond  CGI_InfoNR__ext0O__F1F2_cond2 CGI_InfoNR__ext0O__F2F1_cond.
Opaque CGI_InfoNR__ext0O__cond CGI_InfoNR__ext0O__Format.

Definition CGI_InfoNR__ext0__check_all_none (b : CGI_InfoNR__ext0O__Type) : bool :=
match b with 
  | make__CGI_InfoNR__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CGI_InfoNR__ext0__Format : T_Format CGI_InfoNR__ext0__Type CGI_InfoNR__ext0__cond :=
  restrict_add_format CGI_InfoNR__ext0__check_all_none CGI_InfoNR__ext0O__Format.

Opaque CGI_InfoNR__ext0__cond CGI_InfoNR__ext0__Format.

Definition CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Format : T_Format CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__nat__Format CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F1 CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F2 CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F1F2 CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__F2F1.

Opaque CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__cond CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Format.


Definition CGI_InfoNR__ext1O__Format_Type := Eval cbn in seq_format_prod CGI_InfoNR__ext1O__list.
Definition CGI_InfoNR__ext1O__Format_list : CGI_InfoNR__ext1O__Format_Type :=
  (CGI_InfoNR__ext1O__cellReservedForOtherUse_r16__Format, unit_format).
Definition CGI_InfoNR__ext1O__list__Format := (*Eval compute in *) seq_format CGI_InfoNR__ext1O__list CGI_InfoNR__ext1O__Format_list.
Definition CGI_InfoNR__ext1O__F1 z :=
  (CGI_InfoNR__ext1O__cellReservedForOtherUse_r16 z, tt).
Definition CGI_InfoNR__ext1O__F2 (y : seq_type CGI_InfoNR__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__CGI_InfoNR__ext1O__Type i0
  end.
Lemma CGI_InfoNR__ext1O__F1F2_cond (z : CGI_InfoNR__ext1O__Type)
  : CGI_InfoNR__ext1O__cond z ->
  (seq_cond CGI_InfoNR__ext1O__list (CGI_InfoNR__ext1O__F1 z)).
intro H. unfold CGI_InfoNR__ext1O__cond in H. simpl. auto. Qed.
Lemma CGI_InfoNR__ext1O__F1F2_cond2 (z : CGI_InfoNR__ext1O__Type)
 : CGI_InfoNR__ext1O__F2 (CGI_InfoNR__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CGI_InfoNR__ext1O__F2F1_cond (y : seq_type CGI_InfoNR__ext1O__list)
  : seq_cond CGI_InfoNR__ext1O__list y ->
 (CGI_InfoNR__ext1O__cond (CGI_InfoNR__ext1O__F2 y)) /\  CGI_InfoNR__ext1O__F1 (CGI_InfoNR__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CGI_InfoNR__ext1O__cond. simpl in *. auto.
 - simpl. unfold CGI_InfoNR__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CGI_InfoNR__ext1O__Format : T_Format CGI_InfoNR__ext1O__Type CGI_InfoNR__ext1O__cond :=
        proj2_format  CGI_InfoNR__ext1O__cond CGI_InfoNR__ext1O__list__Format
    CGI_InfoNR__ext1O__F1 CGI_InfoNR__ext1O__F2 CGI_InfoNR__ext1O__F1F2_cond  CGI_InfoNR__ext1O__F1F2_cond2 CGI_InfoNR__ext1O__F2F1_cond.
Opaque CGI_InfoNR__ext1O__cond CGI_InfoNR__ext1O__Format.

Definition CGI_InfoNR__ext1__check_all_none (b : CGI_InfoNR__ext1O__Type) : bool :=
match b with 
  | make__CGI_InfoNR__ext1O__Type None  => false 
  | _ => true 
 end.
Definition CGI_InfoNR__ext1__Format : T_Format CGI_InfoNR__ext1__Type CGI_InfoNR__ext1__cond :=
  restrict_add_format CGI_InfoNR__ext1__check_all_none CGI_InfoNR__ext1O__Format.

Opaque CGI_InfoNR__ext1__cond CGI_InfoNR__ext1__Format.


Definition CGI_InfoNR__root_Format_Type := Eval cbn in seq_format_prod CGI_InfoNR__root_list.
Definition CGI_InfoNR__root_Format_list : CGI_InfoNR__root_Format_Type :=
  (PLMN_IdentityInfoList__Format, (MultiFrequencyBandListNR__Format, (CGI_InfoNR__noSIB1__Format, unit_format))).

Definition CGI_InfoNR__ext_Format_Type := Eval cbn in get_formats CGI_InfoNR__ext_list.
Definition CGI_InfoNR__ext_Format_list : CGI_InfoNR__ext_Format_Type :=
  (CGI_InfoNR__ext0__Format, (CGI_InfoNR__ext1__Format, unit__Format)).

Definition CGI_InfoNR__list_type : Set := (seq_type CGI_InfoNR__root_list) * (seq_ext_type CGI_InfoNR__ext_list).
Definition CGI_InfoNR__list_cond (z : CGI_InfoNR__list_type) : Prop :=
        (seq_cond CGI_InfoNR__root_list (fst z)) /\ (seq_ext_cond CGI_InfoNR__ext_list (snd z)).
Definition CGI_InfoNR__list_format : T_Format CGI_InfoNR__list_type CGI_InfoNR__list_cond :=
 (* Eval compute in *) seq_ext_format CGI_InfoNR__root_list CGI_InfoNR__root_Format_list CGI_InfoNR__ext_list CGI_InfoNR__ext_Format_list.

Opaque CGI_InfoNR__list_format.
Definition CGI_InfoNR__F1 (z : CGI_InfoNR__Type) : CGI_InfoNR__list_type :=
  (((CGI_InfoNR__plmn_IdentityInfoList z, (CGI_InfoNR__frequencyBandList z, (CGI_InfoNR__noSIB1 z, tt)))), (
(CGI_InfoNR__ext0 z, (CGI_InfoNR__ext1 z, tt)))).
Definition CGI_InfoNR__F2 (y : CGI_InfoNR__list_type) : CGI_InfoNR__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, _)))=>
    make__CGI_InfoNR__Type j0 j1 j2 i0 i1
  end.
Definition CGI_InfoNR__helper1 : (forall a : CGI_InfoNR__Type, CGI_InfoNR__cond a -> CGI_InfoNR__list_cond (CGI_InfoNR__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CGI_InfoNR__helper2 : (forall a : CGI_InfoNR__Type, CGI_InfoNR__F2 (CGI_InfoNR__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CGI_InfoNR__helper3 : (forall b : CGI_InfoNR__list_type, CGI_InfoNR__list_cond b -> CGI_InfoNR__cond (CGI_InfoNR__F2 b) /\ CGI_InfoNR__F1 (CGI_InfoNR__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CGI_InfoNR__cond, CGI_InfoNR__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CGI_InfoNR__Format : T_Format CGI_InfoNR__Type CGI_InfoNR__cond :=
 proj2_format CGI_InfoNR__cond CGI_InfoNR__list_format  CGI_InfoNR__F1 CGI_InfoNR__F2 CGI_InfoNR__helper1 CGI_InfoNR__helper2 CGI_InfoNR__helper3.

Opaque CGI_InfoNR__cond CGI_InfoNR__Format.

