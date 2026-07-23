Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NPN_Identity_r16.

Opaque NPN_Identity_r16__cond NPN_Identity_r16__Format.

Definition NPN_IdentityInfo_r16__npn_IdentityList_r16__Type := list NPN_Identity_r16__Type.

Lemma NPN_IdentityInfo_r16__npn_IdentityList_r16__helper1 : (0 <= 1 <= maxNPN_r16)%Z. unfold maxNPN_r16.
 lia. Qed.
Lemma NPN_IdentityInfo_r16__npn_IdentityList_r16__helper2 : to_bit_sz (Z.to_nat (maxNPN_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNPN_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NPN_IdentityInfo_r16__npn_IdentityList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NPN_IdentityInfo_r16__npn_IdentityList_r16__cond (z : NPN_IdentityInfo_r16__npn_IdentityList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNPN_r16)%Z /\ (list_and NPN_Identity_r16__cond z) .

Require Import NR.TrackingAreaCode.

Opaque TrackingAreaCode__cond TrackingAreaCode__Format.

Require Import NR.RAN_AreaCode.

Opaque RAN_AreaCode__cond RAN_AreaCode__Format.

Require Import NR.CellIdentity.

Opaque CellIdentity__cond CellIdentity__Format.

Inductive NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type : Set :=
 | NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__reserved
 | NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__notReserved
.
Definition NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__cond := (fun (_ : NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type) => True).
Lemma NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__nat__helper.

Definition NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F1 t :=
  match t with
  | NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__reserved => 0
  | NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__notReserved => 1
  end.
Definition NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F2 n :=
  match n with
  | 0 => NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__reserved
  | 1 => NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__notReserved
  | _ => NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__reserved
  end.
Lemma NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F1F2 : forall x : NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type, (NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F1 x <= 1) /\ NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F2 (NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F1 x) = x. imp_solve. Qed.
Lemma NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F2F1 : forall (y : nat) (H : y <= 1), NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F1 (NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F2 y) = y. enum_solve H y. Qed.

Inductive NPN_IdentityInfo_r16__iab_Support_r16__Type : Set :=
 | NPN_IdentityInfo_r16__iab_Support_r16__true
.
Definition NPN_IdentityInfo_r16__iab_Support_r16__cond := (fun (_ : NPN_IdentityInfo_r16__iab_Support_r16__Type) => True).
Lemma NPN_IdentityInfo_r16__iab_Support_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NPN_IdentityInfo_r16__iab_Support_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 NPN_IdentityInfo_r16__iab_Support_r16__nat__helper.

Definition NPN_IdentityInfo_r16__iab_Support_r16__F1 t :=
  match t with
  | NPN_IdentityInfo_r16__iab_Support_r16__true => 0
  end.
Definition NPN_IdentityInfo_r16__iab_Support_r16__F2 n :=
  match n with
  | 0 => NPN_IdentityInfo_r16__iab_Support_r16__true
  | _ => NPN_IdentityInfo_r16__iab_Support_r16__true
  end.
Lemma NPN_IdentityInfo_r16__iab_Support_r16__F1F2 : forall x : NPN_IdentityInfo_r16__iab_Support_r16__Type, (NPN_IdentityInfo_r16__iab_Support_r16__F1 x <= 0) /\ NPN_IdentityInfo_r16__iab_Support_r16__F2 (NPN_IdentityInfo_r16__iab_Support_r16__F1 x) = x. imp_solve. Qed.
Lemma NPN_IdentityInfo_r16__iab_Support_r16__F2F1 : forall (y : nat) (H : y <= 0), NPN_IdentityInfo_r16__iab_Support_r16__F1 (NPN_IdentityInfo_r16__iab_Support_r16__F2 y) = y. enum_solve H y. Qed.

Lemma NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__helper1 : (22 <= 32)%Z.  lia. Qed.
Lemma NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__helper2 : to_bit_sz (Z.to_nat (32 - 22)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 22))%Z). { apply Zorder.Zle_minus_le_0. apply NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__Type := Z.
Definition NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__cond := (fun z => (22 <= z <= 32)%Z).
Record NPN_IdentityInfo_r16__ext0O__Type : Set :=
  make__NPN_IdentityInfo_r16__ext0O__Type {
    NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17 : option Z ;
}.
Definition NPN_IdentityInfo_r16__ext0O__list := (
 Opt Z NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__cond ::
 nil).
Definition NPN_IdentityInfo_r16__ext0O__cond z := 
  opt_cond NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__cond (NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17 z) /\
  True.

Definition NPN_IdentityInfo_r16__ext0__Type := NPN_IdentityInfo_r16__ext0O__Type.
Definition NPN_IdentityInfo_r16__ext0__cond := NPN_IdentityInfo_r16__ext0O__cond.

Record NPN_IdentityInfo_r16__Type : Set :=
  make__NPN_IdentityInfo_r16__Type {
    NPN_IdentityInfo_r16__npn_IdentityList_r16 : NPN_IdentityInfo_r16__npn_IdentityList_r16__Type ;
    NPN_IdentityInfo_r16__trackingAreaCode_r16 : TrackingAreaCode__Type ;
    NPN_IdentityInfo_r16__ranac_r16 : option RAN_AreaCode__Type ;
    NPN_IdentityInfo_r16__cellIdentity_r16 : CellIdentity__Type ;
    NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16 : NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type ;
    NPN_IdentityInfo_r16__iab_Support_r16 : option NPN_IdentityInfo_r16__iab_Support_r16__Type ;
    NPN_IdentityInfo_r16__ext0 : option NPN_IdentityInfo_r16__ext0__Type ;
}.
Definition NPN_IdentityInfo_r16__root_list : list seq_elem := (
 Nor NPN_IdentityInfo_r16__npn_IdentityList_r16__Type NPN_IdentityInfo_r16__npn_IdentityList_r16__cond ::
 Nor TrackingAreaCode__Type TrackingAreaCode__cond ::
 Opt RAN_AreaCode__Type RAN_AreaCode__cond ::
 Nor CellIdentity__Type CellIdentity__cond ::
 Nor NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__cond ::
 Opt NPN_IdentityInfo_r16__iab_Support_r16__Type NPN_IdentityInfo_r16__iab_Support_r16__cond ::
 nil).
Definition NPN_IdentityInfo_r16__ext_list : list typ := (
  typ_cons NPN_IdentityInfo_r16__ext0__Type NPN_IdentityInfo_r16__ext0__cond ::
  nil).
Definition NPN_IdentityInfo_r16__cond (z : NPN_IdentityInfo_r16__Type) := 
(  NPN_IdentityInfo_r16__npn_IdentityList_r16__cond (NPN_IdentityInfo_r16__npn_IdentityList_r16 z) /\
  TrackingAreaCode__cond (NPN_IdentityInfo_r16__trackingAreaCode_r16 z) /\
  opt_cond RAN_AreaCode__cond (NPN_IdentityInfo_r16__ranac_r16 z) /\
  CellIdentity__cond (NPN_IdentityInfo_r16__cellIdentity_r16 z) /\
  NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__cond (NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16 z) /\
  opt_cond NPN_IdentityInfo_r16__iab_Support_r16__cond (NPN_IdentityInfo_r16__iab_Support_r16 z) /\
  True) /\ 
(  opt_cond NPN_IdentityInfo_r16__ext0__cond (NPN_IdentityInfo_r16__ext0 z) /\
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
Definition NPN_IdentityInfo_r16__npn_IdentityList_r16__Format : T_Format NPN_IdentityInfo_r16__npn_IdentityList_r16__Type NPN_IdentityInfo_r16__npn_IdentityList_r16__cond := seq_of_format NPN_Identity_r16__Format 1 maxNPN_r16 NPN_IdentityInfo_r16__npn_IdentityList_r16__helper1 NPN_IdentityInfo_r16__npn_IdentityList_r16__helper2.

Opaque NPN_IdentityInfo_r16__npn_IdentityList_r16__cond NPN_IdentityInfo_r16__npn_IdentityList_r16__Format.

Definition NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Format : T_Format NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__nat__Format NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F1 NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F2 NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F1F2 NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__F2F1.

Opaque NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__cond NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Format.

Definition NPN_IdentityInfo_r16__iab_Support_r16__Format : T_Format NPN_IdentityInfo_r16__iab_Support_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NPN_IdentityInfo_r16__iab_Support_r16__nat__Format NPN_IdentityInfo_r16__iab_Support_r16__F1 NPN_IdentityInfo_r16__iab_Support_r16__F2 NPN_IdentityInfo_r16__iab_Support_r16__F1F2 NPN_IdentityInfo_r16__iab_Support_r16__F2F1.

Opaque NPN_IdentityInfo_r16__iab_Support_r16__cond NPN_IdentityInfo_r16__iab_Support_r16__Format.

Definition NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__Format : T_Format Z NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__cond :=
 ranged_int_format (22) (32) NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__helper1 NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__helper2.

Opaque NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__cond NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__Format.


Definition NPN_IdentityInfo_r16__ext0O__Format_Type := Eval cbn in seq_format_prod NPN_IdentityInfo_r16__ext0O__list.
Definition NPN_IdentityInfo_r16__ext0O__Format_list : NPN_IdentityInfo_r16__ext0O__Format_Type :=
  (NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17__Format, unit_format).
Definition NPN_IdentityInfo_r16__ext0O__list__Format := (*Eval compute in *) seq_format NPN_IdentityInfo_r16__ext0O__list NPN_IdentityInfo_r16__ext0O__Format_list.
Definition NPN_IdentityInfo_r16__ext0O__F1 z :=
  (NPN_IdentityInfo_r16__ext0O__gNB_ID_Length_r17 z, tt).
Definition NPN_IdentityInfo_r16__ext0O__F2 (y : seq_type NPN_IdentityInfo_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__NPN_IdentityInfo_r16__ext0O__Type i0
  end.
Lemma NPN_IdentityInfo_r16__ext0O__F1F2_cond (z : NPN_IdentityInfo_r16__ext0O__Type)
  : NPN_IdentityInfo_r16__ext0O__cond z ->
  (seq_cond NPN_IdentityInfo_r16__ext0O__list (NPN_IdentityInfo_r16__ext0O__F1 z)).
intro H. unfold NPN_IdentityInfo_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma NPN_IdentityInfo_r16__ext0O__F1F2_cond2 (z : NPN_IdentityInfo_r16__ext0O__Type)
 : NPN_IdentityInfo_r16__ext0O__F2 (NPN_IdentityInfo_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NPN_IdentityInfo_r16__ext0O__F2F1_cond (y : seq_type NPN_IdentityInfo_r16__ext0O__list)
  : seq_cond NPN_IdentityInfo_r16__ext0O__list y ->
 (NPN_IdentityInfo_r16__ext0O__cond (NPN_IdentityInfo_r16__ext0O__F2 y)) /\  NPN_IdentityInfo_r16__ext0O__F1 (NPN_IdentityInfo_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NPN_IdentityInfo_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold NPN_IdentityInfo_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NPN_IdentityInfo_r16__ext0O__Format : T_Format NPN_IdentityInfo_r16__ext0O__Type NPN_IdentityInfo_r16__ext0O__cond :=
        proj2_format  NPN_IdentityInfo_r16__ext0O__cond NPN_IdentityInfo_r16__ext0O__list__Format
    NPN_IdentityInfo_r16__ext0O__F1 NPN_IdentityInfo_r16__ext0O__F2 NPN_IdentityInfo_r16__ext0O__F1F2_cond  NPN_IdentityInfo_r16__ext0O__F1F2_cond2 NPN_IdentityInfo_r16__ext0O__F2F1_cond.
Opaque NPN_IdentityInfo_r16__ext0O__cond NPN_IdentityInfo_r16__ext0O__Format.

Definition NPN_IdentityInfo_r16__ext0__check_all_none (b : NPN_IdentityInfo_r16__ext0O__Type) : bool :=
match b with 
  | make__NPN_IdentityInfo_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition NPN_IdentityInfo_r16__ext0__Format : T_Format NPN_IdentityInfo_r16__ext0__Type NPN_IdentityInfo_r16__ext0__cond :=
  restrict_add_format NPN_IdentityInfo_r16__ext0__check_all_none NPN_IdentityInfo_r16__ext0O__Format.

Opaque NPN_IdentityInfo_r16__ext0__cond NPN_IdentityInfo_r16__ext0__Format.


Definition NPN_IdentityInfo_r16__root_Format_Type := Eval cbn in seq_format_prod NPN_IdentityInfo_r16__root_list.
Definition NPN_IdentityInfo_r16__root_Format_list : NPN_IdentityInfo_r16__root_Format_Type :=
  (NPN_IdentityInfo_r16__npn_IdentityList_r16__Format, (TrackingAreaCode__Format, (RAN_AreaCode__Format, (CellIdentity__Format, (NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16__Format, (NPN_IdentityInfo_r16__iab_Support_r16__Format, unit_format)))))).

Definition NPN_IdentityInfo_r16__ext_Format_Type := Eval cbn in get_formats NPN_IdentityInfo_r16__ext_list.
Definition NPN_IdentityInfo_r16__ext_Format_list : NPN_IdentityInfo_r16__ext_Format_Type :=
  (NPN_IdentityInfo_r16__ext0__Format, unit__Format).

Definition NPN_IdentityInfo_r16__list_type : Set := (seq_type NPN_IdentityInfo_r16__root_list) * (seq_ext_type NPN_IdentityInfo_r16__ext_list).
Definition NPN_IdentityInfo_r16__list_cond (z : NPN_IdentityInfo_r16__list_type) : Prop :=
        (seq_cond NPN_IdentityInfo_r16__root_list (fst z)) /\ (seq_ext_cond NPN_IdentityInfo_r16__ext_list (snd z)).
Definition NPN_IdentityInfo_r16__list_format : T_Format NPN_IdentityInfo_r16__list_type NPN_IdentityInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format NPN_IdentityInfo_r16__root_list NPN_IdentityInfo_r16__root_Format_list NPN_IdentityInfo_r16__ext_list NPN_IdentityInfo_r16__ext_Format_list.

Opaque NPN_IdentityInfo_r16__list_format.
Definition NPN_IdentityInfo_r16__F1 (z : NPN_IdentityInfo_r16__Type) : NPN_IdentityInfo_r16__list_type :=
  (((NPN_IdentityInfo_r16__npn_IdentityList_r16 z, (NPN_IdentityInfo_r16__trackingAreaCode_r16 z, (NPN_IdentityInfo_r16__ranac_r16 z, (NPN_IdentityInfo_r16__cellIdentity_r16 z, (NPN_IdentityInfo_r16__cellReservedForOperatorUse_r16 z, (NPN_IdentityInfo_r16__iab_Support_r16 z, tt))))))), (
(NPN_IdentityInfo_r16__ext0 z, tt))).
Definition NPN_IdentityInfo_r16__F2 (y : NPN_IdentityInfo_r16__list_type) : NPN_IdentityInfo_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, _))=>
    make__NPN_IdentityInfo_r16__Type j0 j1 j2 j3 j4 j5 i0
  end.
Definition NPN_IdentityInfo_r16__helper1 : (forall a : NPN_IdentityInfo_r16__Type, NPN_IdentityInfo_r16__cond a -> NPN_IdentityInfo_r16__list_cond (NPN_IdentityInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NPN_IdentityInfo_r16__helper2 : (forall a : NPN_IdentityInfo_r16__Type, NPN_IdentityInfo_r16__F2 (NPN_IdentityInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NPN_IdentityInfo_r16__helper3 : (forall b : NPN_IdentityInfo_r16__list_type, NPN_IdentityInfo_r16__list_cond b -> NPN_IdentityInfo_r16__cond (NPN_IdentityInfo_r16__F2 b) /\ NPN_IdentityInfo_r16__F1 (NPN_IdentityInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NPN_IdentityInfo_r16__cond, NPN_IdentityInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NPN_IdentityInfo_r16__Format : T_Format NPN_IdentityInfo_r16__Type NPN_IdentityInfo_r16__cond :=
 proj2_format NPN_IdentityInfo_r16__cond NPN_IdentityInfo_r16__list_format  NPN_IdentityInfo_r16__F1 NPN_IdentityInfo_r16__F2 NPN_IdentityInfo_r16__helper1 NPN_IdentityInfo_r16__helper2 NPN_IdentityInfo_r16__helper3.

Opaque NPN_IdentityInfo_r16__cond NPN_IdentityInfo_r16__Format.

