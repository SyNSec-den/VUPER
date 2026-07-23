Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_IdentityInfoList.

Opaque PLMN_IdentityInfoList__cond PLMN_IdentityInfoList__Format.

Inductive CellAccessRelatedInfo__cellReservedForOtherUse__Type : Set :=
 | CellAccessRelatedInfo__cellReservedForOtherUse__true
.
Definition CellAccessRelatedInfo__cellReservedForOtherUse__cond := (fun (_ : CellAccessRelatedInfo__cellReservedForOtherUse__Type) => True).
Lemma CellAccessRelatedInfo__cellReservedForOtherUse__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellAccessRelatedInfo__cellReservedForOtherUse__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CellAccessRelatedInfo__cellReservedForOtherUse__nat__helper.

Definition CellAccessRelatedInfo__cellReservedForOtherUse__F1 t :=
  match t with
  | CellAccessRelatedInfo__cellReservedForOtherUse__true => 0
  end.
Definition CellAccessRelatedInfo__cellReservedForOtherUse__F2 n :=
  match n with
  | 0 => CellAccessRelatedInfo__cellReservedForOtherUse__true
  | _ => CellAccessRelatedInfo__cellReservedForOtherUse__true
  end.
Lemma CellAccessRelatedInfo__cellReservedForOtherUse__F1F2 : forall x : CellAccessRelatedInfo__cellReservedForOtherUse__Type, (CellAccessRelatedInfo__cellReservedForOtherUse__F1 x <= 0) /\ CellAccessRelatedInfo__cellReservedForOtherUse__F2 (CellAccessRelatedInfo__cellReservedForOtherUse__F1 x) = x. imp_solve. Qed.
Lemma CellAccessRelatedInfo__cellReservedForOtherUse__F2F1 : forall (y : nat) (H : y <= 0), CellAccessRelatedInfo__cellReservedForOtherUse__F1 (CellAccessRelatedInfo__cellReservedForOtherUse__F2 y) = y. enum_solve H y. Qed.

Inductive CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Type : Set :=
 | CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__true
.
Definition CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__cond := (fun (_ : CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Type) => True).
Lemma CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__nat__helper.

Definition CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F1 t :=
  match t with
  | CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__true => 0
  end.
Definition CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F2 n :=
  match n with
  | 0 => CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__true
  | _ => CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__true
  end.
Lemma CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F1F2 : forall x : CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Type, (CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F1 x <= 0) /\ CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F2 (CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F1 x) = x. imp_solve. Qed.
Lemma CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F2F1 : forall (y : nat) (H : y <= 0), CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F1 (CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.NPN_IdentityInfoList_r16.

Opaque NPN_IdentityInfoList_r16__cond NPN_IdentityInfoList_r16__Format.

Record CellAccessRelatedInfo__ext0O__Type : Set :=
  make__CellAccessRelatedInfo__ext0O__Type {
    CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16 : option CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Type ;
    CellAccessRelatedInfo__ext0O__npn_IdentityInfoList_r16 : option NPN_IdentityInfoList_r16__Type ;
}.
Definition CellAccessRelatedInfo__ext0O__list := (
 Opt CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Type CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__cond ::
 Opt NPN_IdentityInfoList_r16__Type NPN_IdentityInfoList_r16__cond ::
 nil).
Definition CellAccessRelatedInfo__ext0O__cond z := 
  opt_cond CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__cond (CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16 z) /\
  opt_cond NPN_IdentityInfoList_r16__cond (CellAccessRelatedInfo__ext0O__npn_IdentityInfoList_r16 z) /\
  True.

Definition CellAccessRelatedInfo__ext0__Type := CellAccessRelatedInfo__ext0O__Type.
Definition CellAccessRelatedInfo__ext0__cond := CellAccessRelatedInfo__ext0O__cond.

Require Import NR.SNPN_AccessInfo_r17.

Opaque SNPN_AccessInfo_r17__cond SNPN_AccessInfo_r17__Format.

Definition CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__Type := list SNPN_AccessInfo_r17__Type.

Lemma CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__helper1 : (0 <= 1 <= maxNPN_r16)%Z. unfold maxNPN_r16.
 lia. Qed.
Lemma CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__helper2 : to_bit_sz (Z.to_nat (maxNPN_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNPN_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__cond (z : CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNPN_r16)%Z /\ (list_and SNPN_AccessInfo_r17__cond z) .

Record CellAccessRelatedInfo__ext1O__Type : Set :=
  make__CellAccessRelatedInfo__ext1O__Type {
    CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17 : option CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__Type ;
}.
Definition CellAccessRelatedInfo__ext1O__list := (
 Opt CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__Type CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__cond ::
 nil).
Definition CellAccessRelatedInfo__ext1O__cond z := 
  opt_cond CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__cond (CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17 z) /\
  True.

Definition CellAccessRelatedInfo__ext1__Type := CellAccessRelatedInfo__ext1O__Type.
Definition CellAccessRelatedInfo__ext1__cond := CellAccessRelatedInfo__ext1O__cond.

Record CellAccessRelatedInfo__Type : Set :=
  make__CellAccessRelatedInfo__Type {
    CellAccessRelatedInfo__plmn_IdentityInfoList : PLMN_IdentityInfoList__Type ;
    CellAccessRelatedInfo__cellReservedForOtherUse : option CellAccessRelatedInfo__cellReservedForOtherUse__Type ;
    CellAccessRelatedInfo__ext0 : option CellAccessRelatedInfo__ext0__Type ;
    CellAccessRelatedInfo__ext1 : option CellAccessRelatedInfo__ext1__Type ;
}.
Definition CellAccessRelatedInfo__root_list : list seq_elem := (
 Nor PLMN_IdentityInfoList__Type PLMN_IdentityInfoList__cond ::
 Opt CellAccessRelatedInfo__cellReservedForOtherUse__Type CellAccessRelatedInfo__cellReservedForOtherUse__cond ::
 nil).
Definition CellAccessRelatedInfo__ext_list : list typ := (
  typ_cons CellAccessRelatedInfo__ext0__Type CellAccessRelatedInfo__ext0__cond ::
  typ_cons CellAccessRelatedInfo__ext1__Type CellAccessRelatedInfo__ext1__cond ::
  nil).
Definition CellAccessRelatedInfo__cond (z : CellAccessRelatedInfo__Type) := 
(  PLMN_IdentityInfoList__cond (CellAccessRelatedInfo__plmn_IdentityInfoList z) /\
  opt_cond CellAccessRelatedInfo__cellReservedForOtherUse__cond (CellAccessRelatedInfo__cellReservedForOtherUse z) /\
  True) /\ 
(  opt_cond CellAccessRelatedInfo__ext0__cond (CellAccessRelatedInfo__ext0 z) /\
  opt_cond CellAccessRelatedInfo__ext1__cond (CellAccessRelatedInfo__ext1 z) /\
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
Definition CellAccessRelatedInfo__cellReservedForOtherUse__Format : T_Format CellAccessRelatedInfo__cellReservedForOtherUse__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellAccessRelatedInfo__cellReservedForOtherUse__nat__Format CellAccessRelatedInfo__cellReservedForOtherUse__F1 CellAccessRelatedInfo__cellReservedForOtherUse__F2 CellAccessRelatedInfo__cellReservedForOtherUse__F1F2 CellAccessRelatedInfo__cellReservedForOtherUse__F2F1.

Opaque CellAccessRelatedInfo__cellReservedForOtherUse__cond CellAccessRelatedInfo__cellReservedForOtherUse__Format.

Definition CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Format : T_Format CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__nat__Format CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F1 CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F2 CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F1F2 CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__F2F1.

Opaque CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__cond CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Format.


Definition CellAccessRelatedInfo__ext0O__Format_Type := Eval cbn in seq_format_prod CellAccessRelatedInfo__ext0O__list.
Definition CellAccessRelatedInfo__ext0O__Format_list : CellAccessRelatedInfo__ext0O__Format_Type :=
  (CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16__Format, (NPN_IdentityInfoList_r16__Format, unit_format)).
Definition CellAccessRelatedInfo__ext0O__list__Format := (*Eval compute in *) seq_format CellAccessRelatedInfo__ext0O__list CellAccessRelatedInfo__ext0O__Format_list.
Definition CellAccessRelatedInfo__ext0O__F1 z :=
  (CellAccessRelatedInfo__ext0O__cellReservedForFutureUse_r16 z, (CellAccessRelatedInfo__ext0O__npn_IdentityInfoList_r16 z, tt)).
Definition CellAccessRelatedInfo__ext0O__F2 (y : seq_type CellAccessRelatedInfo__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CellAccessRelatedInfo__ext0O__Type i0 i1
  end.
Lemma CellAccessRelatedInfo__ext0O__F1F2_cond (z : CellAccessRelatedInfo__ext0O__Type)
  : CellAccessRelatedInfo__ext0O__cond z ->
  (seq_cond CellAccessRelatedInfo__ext0O__list (CellAccessRelatedInfo__ext0O__F1 z)).
intro H. unfold CellAccessRelatedInfo__ext0O__cond in H. simpl. auto. Qed.
Lemma CellAccessRelatedInfo__ext0O__F1F2_cond2 (z : CellAccessRelatedInfo__ext0O__Type)
 : CellAccessRelatedInfo__ext0O__F2 (CellAccessRelatedInfo__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellAccessRelatedInfo__ext0O__F2F1_cond (y : seq_type CellAccessRelatedInfo__ext0O__list)
  : seq_cond CellAccessRelatedInfo__ext0O__list y ->
 (CellAccessRelatedInfo__ext0O__cond (CellAccessRelatedInfo__ext0O__F2 y)) /\  CellAccessRelatedInfo__ext0O__F1 (CellAccessRelatedInfo__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellAccessRelatedInfo__ext0O__cond. simpl in *. auto.
 - simpl. unfold CellAccessRelatedInfo__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellAccessRelatedInfo__ext0O__Format : T_Format CellAccessRelatedInfo__ext0O__Type CellAccessRelatedInfo__ext0O__cond :=
        proj2_format  CellAccessRelatedInfo__ext0O__cond CellAccessRelatedInfo__ext0O__list__Format
    CellAccessRelatedInfo__ext0O__F1 CellAccessRelatedInfo__ext0O__F2 CellAccessRelatedInfo__ext0O__F1F2_cond  CellAccessRelatedInfo__ext0O__F1F2_cond2 CellAccessRelatedInfo__ext0O__F2F1_cond.
Opaque CellAccessRelatedInfo__ext0O__cond CellAccessRelatedInfo__ext0O__Format.

Definition CellAccessRelatedInfo__ext0__check_all_none (b : CellAccessRelatedInfo__ext0O__Type) : bool :=
match b with 
  | make__CellAccessRelatedInfo__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition CellAccessRelatedInfo__ext0__Format : T_Format CellAccessRelatedInfo__ext0__Type CellAccessRelatedInfo__ext0__cond :=
  restrict_add_format CellAccessRelatedInfo__ext0__check_all_none CellAccessRelatedInfo__ext0O__Format.

Opaque CellAccessRelatedInfo__ext0__cond CellAccessRelatedInfo__ext0__Format.

Definition CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__Format : T_Format CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__Type CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__cond := seq_of_format SNPN_AccessInfo_r17__Format 1 maxNPN_r16 CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__helper1 CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__helper2.

Opaque CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__cond CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__Format.


Definition CellAccessRelatedInfo__ext1O__Format_Type := Eval cbn in seq_format_prod CellAccessRelatedInfo__ext1O__list.
Definition CellAccessRelatedInfo__ext1O__Format_list : CellAccessRelatedInfo__ext1O__Format_Type :=
  (CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17__Format, unit_format).
Definition CellAccessRelatedInfo__ext1O__list__Format := (*Eval compute in *) seq_format CellAccessRelatedInfo__ext1O__list CellAccessRelatedInfo__ext1O__Format_list.
Definition CellAccessRelatedInfo__ext1O__F1 z :=
  (CellAccessRelatedInfo__ext1O__snpn_AccessInfoList_r17 z, tt).
Definition CellAccessRelatedInfo__ext1O__F2 (y : seq_type CellAccessRelatedInfo__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__CellAccessRelatedInfo__ext1O__Type i0
  end.
Lemma CellAccessRelatedInfo__ext1O__F1F2_cond (z : CellAccessRelatedInfo__ext1O__Type)
  : CellAccessRelatedInfo__ext1O__cond z ->
  (seq_cond CellAccessRelatedInfo__ext1O__list (CellAccessRelatedInfo__ext1O__F1 z)).
intro H. unfold CellAccessRelatedInfo__ext1O__cond in H. simpl. auto. Qed.
Lemma CellAccessRelatedInfo__ext1O__F1F2_cond2 (z : CellAccessRelatedInfo__ext1O__Type)
 : CellAccessRelatedInfo__ext1O__F2 (CellAccessRelatedInfo__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellAccessRelatedInfo__ext1O__F2F1_cond (y : seq_type CellAccessRelatedInfo__ext1O__list)
  : seq_cond CellAccessRelatedInfo__ext1O__list y ->
 (CellAccessRelatedInfo__ext1O__cond (CellAccessRelatedInfo__ext1O__F2 y)) /\  CellAccessRelatedInfo__ext1O__F1 (CellAccessRelatedInfo__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellAccessRelatedInfo__ext1O__cond. simpl in *. auto.
 - simpl. unfold CellAccessRelatedInfo__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellAccessRelatedInfo__ext1O__Format : T_Format CellAccessRelatedInfo__ext1O__Type CellAccessRelatedInfo__ext1O__cond :=
        proj2_format  CellAccessRelatedInfo__ext1O__cond CellAccessRelatedInfo__ext1O__list__Format
    CellAccessRelatedInfo__ext1O__F1 CellAccessRelatedInfo__ext1O__F2 CellAccessRelatedInfo__ext1O__F1F2_cond  CellAccessRelatedInfo__ext1O__F1F2_cond2 CellAccessRelatedInfo__ext1O__F2F1_cond.
Opaque CellAccessRelatedInfo__ext1O__cond CellAccessRelatedInfo__ext1O__Format.

Definition CellAccessRelatedInfo__ext1__check_all_none (b : CellAccessRelatedInfo__ext1O__Type) : bool :=
match b with 
  | make__CellAccessRelatedInfo__ext1O__Type None  => false 
  | _ => true 
 end.
Definition CellAccessRelatedInfo__ext1__Format : T_Format CellAccessRelatedInfo__ext1__Type CellAccessRelatedInfo__ext1__cond :=
  restrict_add_format CellAccessRelatedInfo__ext1__check_all_none CellAccessRelatedInfo__ext1O__Format.

Opaque CellAccessRelatedInfo__ext1__cond CellAccessRelatedInfo__ext1__Format.


Definition CellAccessRelatedInfo__root_Format_Type := Eval cbn in seq_format_prod CellAccessRelatedInfo__root_list.
Definition CellAccessRelatedInfo__root_Format_list : CellAccessRelatedInfo__root_Format_Type :=
  (PLMN_IdentityInfoList__Format, (CellAccessRelatedInfo__cellReservedForOtherUse__Format, unit_format)).

Definition CellAccessRelatedInfo__ext_Format_Type := Eval cbn in get_formats CellAccessRelatedInfo__ext_list.
Definition CellAccessRelatedInfo__ext_Format_list : CellAccessRelatedInfo__ext_Format_Type :=
  (CellAccessRelatedInfo__ext0__Format, (CellAccessRelatedInfo__ext1__Format, unit__Format)).

Definition CellAccessRelatedInfo__list_type : Set := (seq_type CellAccessRelatedInfo__root_list) * (seq_ext_type CellAccessRelatedInfo__ext_list).
Definition CellAccessRelatedInfo__list_cond (z : CellAccessRelatedInfo__list_type) : Prop :=
        (seq_cond CellAccessRelatedInfo__root_list (fst z)) /\ (seq_ext_cond CellAccessRelatedInfo__ext_list (snd z)).
Definition CellAccessRelatedInfo__list_format : T_Format CellAccessRelatedInfo__list_type CellAccessRelatedInfo__list_cond :=
 (* Eval compute in *) seq_ext_format CellAccessRelatedInfo__root_list CellAccessRelatedInfo__root_Format_list CellAccessRelatedInfo__ext_list CellAccessRelatedInfo__ext_Format_list.

Opaque CellAccessRelatedInfo__list_format.
Definition CellAccessRelatedInfo__F1 (z : CellAccessRelatedInfo__Type) : CellAccessRelatedInfo__list_type :=
  (((CellAccessRelatedInfo__plmn_IdentityInfoList z, (CellAccessRelatedInfo__cellReservedForOtherUse z, tt))), (
(CellAccessRelatedInfo__ext0 z, (CellAccessRelatedInfo__ext1 z, tt)))).
Definition CellAccessRelatedInfo__F2 (y : CellAccessRelatedInfo__list_type) : CellAccessRelatedInfo__Type :=
  match y with
  | ((j0, (j1, _)), (i0, (i1, _)))=>
    make__CellAccessRelatedInfo__Type j0 j1 i0 i1
  end.
Definition CellAccessRelatedInfo__helper1 : (forall a : CellAccessRelatedInfo__Type, CellAccessRelatedInfo__cond a -> CellAccessRelatedInfo__list_cond (CellAccessRelatedInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CellAccessRelatedInfo__helper2 : (forall a : CellAccessRelatedInfo__Type, CellAccessRelatedInfo__F2 (CellAccessRelatedInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CellAccessRelatedInfo__helper3 : (forall b : CellAccessRelatedInfo__list_type, CellAccessRelatedInfo__list_cond b -> CellAccessRelatedInfo__cond (CellAccessRelatedInfo__F2 b) /\ CellAccessRelatedInfo__F1 (CellAccessRelatedInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CellAccessRelatedInfo__cond, CellAccessRelatedInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CellAccessRelatedInfo__Format : T_Format CellAccessRelatedInfo__Type CellAccessRelatedInfo__cond :=
 proj2_format CellAccessRelatedInfo__cond CellAccessRelatedInfo__list_format  CellAccessRelatedInfo__F1 CellAccessRelatedInfo__F2 CellAccessRelatedInfo__helper1 CellAccessRelatedInfo__helper2 CellAccessRelatedInfo__helper3.

Opaque CellAccessRelatedInfo__cond CellAccessRelatedInfo__Format.

