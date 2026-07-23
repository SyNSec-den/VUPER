Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Definition PLMN_IdentityInfo__plmn_IdentityList__Type := list PLMN_Identity__Type.

Lemma PLMN_IdentityInfo__plmn_IdentityList__helper1 : (0 <= 1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma PLMN_IdentityInfo__plmn_IdentityList__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PLMN_IdentityInfo__plmn_IdentityList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PLMN_IdentityInfo__plmn_IdentityList__cond (z : PLMN_IdentityInfo__plmn_IdentityList__Type) :=  (1 <= Z.of_nat (length z) <= maxPLMN)%Z /\ (list_and PLMN_Identity__cond z) .

Require Import NR.TrackingAreaCode.

Opaque TrackingAreaCode__cond TrackingAreaCode__Format.

Require Import NR.RAN_AreaCode.

Opaque RAN_AreaCode__cond RAN_AreaCode__Format.

Require Import NR.CellIdentity.

Opaque CellIdentity__cond CellIdentity__Format.

Inductive PLMN_IdentityInfo__cellReservedForOperatorUse__Type : Set :=
 | PLMN_IdentityInfo__cellReservedForOperatorUse__reserved
 | PLMN_IdentityInfo__cellReservedForOperatorUse__notReserved
.
Definition PLMN_IdentityInfo__cellReservedForOperatorUse__cond := (fun (_ : PLMN_IdentityInfo__cellReservedForOperatorUse__Type) => True).
Lemma PLMN_IdentityInfo__cellReservedForOperatorUse__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PLMN_IdentityInfo__cellReservedForOperatorUse__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PLMN_IdentityInfo__cellReservedForOperatorUse__nat__helper.

Definition PLMN_IdentityInfo__cellReservedForOperatorUse__F1 t :=
  match t with
  | PLMN_IdentityInfo__cellReservedForOperatorUse__reserved => 0
  | PLMN_IdentityInfo__cellReservedForOperatorUse__notReserved => 1
  end.
Definition PLMN_IdentityInfo__cellReservedForOperatorUse__F2 n :=
  match n with
  | 0 => PLMN_IdentityInfo__cellReservedForOperatorUse__reserved
  | 1 => PLMN_IdentityInfo__cellReservedForOperatorUse__notReserved
  | _ => PLMN_IdentityInfo__cellReservedForOperatorUse__reserved
  end.
Lemma PLMN_IdentityInfo__cellReservedForOperatorUse__F1F2 : forall x : PLMN_IdentityInfo__cellReservedForOperatorUse__Type, (PLMN_IdentityInfo__cellReservedForOperatorUse__F1 x <= 1) /\ PLMN_IdentityInfo__cellReservedForOperatorUse__F2 (PLMN_IdentityInfo__cellReservedForOperatorUse__F1 x) = x. imp_solve. Qed.
Lemma PLMN_IdentityInfo__cellReservedForOperatorUse__F2F1 : forall (y : nat) (H : y <= 1), PLMN_IdentityInfo__cellReservedForOperatorUse__F1 (PLMN_IdentityInfo__cellReservedForOperatorUse__F2 y) = y. enum_solve H y. Qed.

Inductive PLMN_IdentityInfo__ext0O__iab_Support_r16__Type : Set :=
 | PLMN_IdentityInfo__ext0O__iab_Support_r16__true
.
Definition PLMN_IdentityInfo__ext0O__iab_Support_r16__cond := (fun (_ : PLMN_IdentityInfo__ext0O__iab_Support_r16__Type) => True).
Lemma PLMN_IdentityInfo__ext0O__iab_Support_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PLMN_IdentityInfo__ext0O__iab_Support_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PLMN_IdentityInfo__ext0O__iab_Support_r16__nat__helper.

Definition PLMN_IdentityInfo__ext0O__iab_Support_r16__F1 t :=
  match t with
  | PLMN_IdentityInfo__ext0O__iab_Support_r16__true => 0
  end.
Definition PLMN_IdentityInfo__ext0O__iab_Support_r16__F2 n :=
  match n with
  | 0 => PLMN_IdentityInfo__ext0O__iab_Support_r16__true
  | _ => PLMN_IdentityInfo__ext0O__iab_Support_r16__true
  end.
Lemma PLMN_IdentityInfo__ext0O__iab_Support_r16__F1F2 : forall x : PLMN_IdentityInfo__ext0O__iab_Support_r16__Type, (PLMN_IdentityInfo__ext0O__iab_Support_r16__F1 x <= 0) /\ PLMN_IdentityInfo__ext0O__iab_Support_r16__F2 (PLMN_IdentityInfo__ext0O__iab_Support_r16__F1 x) = x. imp_solve. Qed.
Lemma PLMN_IdentityInfo__ext0O__iab_Support_r16__F2F1 : forall (y : nat) (H : y <= 0), PLMN_IdentityInfo__ext0O__iab_Support_r16__F1 (PLMN_IdentityInfo__ext0O__iab_Support_r16__F2 y) = y. enum_solve H y. Qed.

Record PLMN_IdentityInfo__ext0O__Type : Set :=
  make__PLMN_IdentityInfo__ext0O__Type {
    PLMN_IdentityInfo__ext0O__iab_Support_r16 : option PLMN_IdentityInfo__ext0O__iab_Support_r16__Type ;
}.
Definition PLMN_IdentityInfo__ext0O__list := (
 Opt PLMN_IdentityInfo__ext0O__iab_Support_r16__Type PLMN_IdentityInfo__ext0O__iab_Support_r16__cond ::
 nil).
Definition PLMN_IdentityInfo__ext0O__cond z := 
  opt_cond PLMN_IdentityInfo__ext0O__iab_Support_r16__cond (PLMN_IdentityInfo__ext0O__iab_Support_r16 z) /\
  True.

Definition PLMN_IdentityInfo__ext0__Type := PLMN_IdentityInfo__ext0O__Type.
Definition PLMN_IdentityInfo__ext0__cond := PLMN_IdentityInfo__ext0O__cond.

Require Import NR.TrackingAreaCode.

Opaque TrackingAreaCode__cond TrackingAreaCode__Format.

Definition PLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type := list TrackingAreaCode__Type.

Lemma PLMN_IdentityInfo__ext1O__trackingAreaList_r17__helper1 : (0 <= 1 <= maxTAC_r17)%Z. unfold maxTAC_r17.
 lia. Qed.
Lemma PLMN_IdentityInfo__ext1O__trackingAreaList_r17__helper2 : to_bit_sz (Z.to_nat (maxTAC_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxTAC_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PLMN_IdentityInfo__ext1O__trackingAreaList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PLMN_IdentityInfo__ext1O__trackingAreaList_r17__cond (z : PLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxTAC_r17)%Z /\ (list_and TrackingAreaCode__cond z) .

Lemma PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__helper1 : (22 <= 32)%Z.  lia. Qed.
Lemma PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__helper2 : to_bit_sz (Z.to_nat (32 - 22)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 22))%Z). { apply Zorder.Zle_minus_le_0. apply PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__Type := Z.
Definition PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__cond := (fun z => (22 <= z <= 32)%Z).
Record PLMN_IdentityInfo__ext1O__Type : Set :=
  make__PLMN_IdentityInfo__ext1O__Type {
    PLMN_IdentityInfo__ext1O__trackingAreaList_r17 : option PLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type ;
    PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17 : option Z ;
}.
Definition PLMN_IdentityInfo__ext1O__list := (
 Opt PLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type PLMN_IdentityInfo__ext1O__trackingAreaList_r17__cond ::
 Opt Z PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__cond ::
 nil).
Definition PLMN_IdentityInfo__ext1O__cond z := 
  opt_cond PLMN_IdentityInfo__ext1O__trackingAreaList_r17__cond (PLMN_IdentityInfo__ext1O__trackingAreaList_r17 z) /\
  opt_cond PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__cond (PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17 z) /\
  True.

Definition PLMN_IdentityInfo__ext1__Type := PLMN_IdentityInfo__ext1O__Type.
Definition PLMN_IdentityInfo__ext1__cond := PLMN_IdentityInfo__ext1O__cond.

Record PLMN_IdentityInfo__Type : Set :=
  make__PLMN_IdentityInfo__Type {
    PLMN_IdentityInfo__plmn_IdentityList : PLMN_IdentityInfo__plmn_IdentityList__Type ;
    PLMN_IdentityInfo__trackingAreaCode : option TrackingAreaCode__Type ;
    PLMN_IdentityInfo__ranac : option RAN_AreaCode__Type ;
    PLMN_IdentityInfo__cellIdentity : CellIdentity__Type ;
    PLMN_IdentityInfo__cellReservedForOperatorUse : PLMN_IdentityInfo__cellReservedForOperatorUse__Type ;
    PLMN_IdentityInfo__ext0 : option PLMN_IdentityInfo__ext0__Type ;
    PLMN_IdentityInfo__ext1 : option PLMN_IdentityInfo__ext1__Type ;
}.
Definition PLMN_IdentityInfo__root_list : list seq_elem := (
 Nor PLMN_IdentityInfo__plmn_IdentityList__Type PLMN_IdentityInfo__plmn_IdentityList__cond ::
 Opt TrackingAreaCode__Type TrackingAreaCode__cond ::
 Opt RAN_AreaCode__Type RAN_AreaCode__cond ::
 Nor CellIdentity__Type CellIdentity__cond ::
 Nor PLMN_IdentityInfo__cellReservedForOperatorUse__Type PLMN_IdentityInfo__cellReservedForOperatorUse__cond ::
 nil).
Definition PLMN_IdentityInfo__ext_list : list typ := (
  typ_cons PLMN_IdentityInfo__ext0__Type PLMN_IdentityInfo__ext0__cond ::
  typ_cons PLMN_IdentityInfo__ext1__Type PLMN_IdentityInfo__ext1__cond ::
  nil).
Definition PLMN_IdentityInfo__cond (z : PLMN_IdentityInfo__Type) := 
(  PLMN_IdentityInfo__plmn_IdentityList__cond (PLMN_IdentityInfo__plmn_IdentityList z) /\
  opt_cond TrackingAreaCode__cond (PLMN_IdentityInfo__trackingAreaCode z) /\
  opt_cond RAN_AreaCode__cond (PLMN_IdentityInfo__ranac z) /\
  CellIdentity__cond (PLMN_IdentityInfo__cellIdentity z) /\
  PLMN_IdentityInfo__cellReservedForOperatorUse__cond (PLMN_IdentityInfo__cellReservedForOperatorUse z) /\
  True) /\ 
(  opt_cond PLMN_IdentityInfo__ext0__cond (PLMN_IdentityInfo__ext0 z) /\
  opt_cond PLMN_IdentityInfo__ext1__cond (PLMN_IdentityInfo__ext1 z) /\
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
Definition PLMN_IdentityInfo__plmn_IdentityList__Format : T_Format PLMN_IdentityInfo__plmn_IdentityList__Type PLMN_IdentityInfo__plmn_IdentityList__cond := seq_of_format PLMN_Identity__Format 1 maxPLMN PLMN_IdentityInfo__plmn_IdentityList__helper1 PLMN_IdentityInfo__plmn_IdentityList__helper2.

Opaque PLMN_IdentityInfo__plmn_IdentityList__cond PLMN_IdentityInfo__plmn_IdentityList__Format.

Definition PLMN_IdentityInfo__cellReservedForOperatorUse__Format : T_Format PLMN_IdentityInfo__cellReservedForOperatorUse__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PLMN_IdentityInfo__cellReservedForOperatorUse__nat__Format PLMN_IdentityInfo__cellReservedForOperatorUse__F1 PLMN_IdentityInfo__cellReservedForOperatorUse__F2 PLMN_IdentityInfo__cellReservedForOperatorUse__F1F2 PLMN_IdentityInfo__cellReservedForOperatorUse__F2F1.

Opaque PLMN_IdentityInfo__cellReservedForOperatorUse__cond PLMN_IdentityInfo__cellReservedForOperatorUse__Format.

Definition PLMN_IdentityInfo__ext0O__iab_Support_r16__Format : T_Format PLMN_IdentityInfo__ext0O__iab_Support_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PLMN_IdentityInfo__ext0O__iab_Support_r16__nat__Format PLMN_IdentityInfo__ext0O__iab_Support_r16__F1 PLMN_IdentityInfo__ext0O__iab_Support_r16__F2 PLMN_IdentityInfo__ext0O__iab_Support_r16__F1F2 PLMN_IdentityInfo__ext0O__iab_Support_r16__F2F1.

Opaque PLMN_IdentityInfo__ext0O__iab_Support_r16__cond PLMN_IdentityInfo__ext0O__iab_Support_r16__Format.


Definition PLMN_IdentityInfo__ext0O__Format_Type := Eval cbn in seq_format_prod PLMN_IdentityInfo__ext0O__list.
Definition PLMN_IdentityInfo__ext0O__Format_list : PLMN_IdentityInfo__ext0O__Format_Type :=
  (PLMN_IdentityInfo__ext0O__iab_Support_r16__Format, unit_format).
Definition PLMN_IdentityInfo__ext0O__list__Format := (*Eval compute in *) seq_format PLMN_IdentityInfo__ext0O__list PLMN_IdentityInfo__ext0O__Format_list.
Definition PLMN_IdentityInfo__ext0O__F1 z :=
  (PLMN_IdentityInfo__ext0O__iab_Support_r16 z, tt).
Definition PLMN_IdentityInfo__ext0O__F2 (y : seq_type PLMN_IdentityInfo__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PLMN_IdentityInfo__ext0O__Type i0
  end.
Lemma PLMN_IdentityInfo__ext0O__F1F2_cond (z : PLMN_IdentityInfo__ext0O__Type)
  : PLMN_IdentityInfo__ext0O__cond z ->
  (seq_cond PLMN_IdentityInfo__ext0O__list (PLMN_IdentityInfo__ext0O__F1 z)).
intro H. unfold PLMN_IdentityInfo__ext0O__cond in H. simpl. auto. Qed.
Lemma PLMN_IdentityInfo__ext0O__F1F2_cond2 (z : PLMN_IdentityInfo__ext0O__Type)
 : PLMN_IdentityInfo__ext0O__F2 (PLMN_IdentityInfo__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PLMN_IdentityInfo__ext0O__F2F1_cond (y : seq_type PLMN_IdentityInfo__ext0O__list)
  : seq_cond PLMN_IdentityInfo__ext0O__list y ->
 (PLMN_IdentityInfo__ext0O__cond (PLMN_IdentityInfo__ext0O__F2 y)) /\  PLMN_IdentityInfo__ext0O__F1 (PLMN_IdentityInfo__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PLMN_IdentityInfo__ext0O__cond. simpl in *. auto.
 - simpl. unfold PLMN_IdentityInfo__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PLMN_IdentityInfo__ext0O__Format : T_Format PLMN_IdentityInfo__ext0O__Type PLMN_IdentityInfo__ext0O__cond :=
        proj2_format  PLMN_IdentityInfo__ext0O__cond PLMN_IdentityInfo__ext0O__list__Format
    PLMN_IdentityInfo__ext0O__F1 PLMN_IdentityInfo__ext0O__F2 PLMN_IdentityInfo__ext0O__F1F2_cond  PLMN_IdentityInfo__ext0O__F1F2_cond2 PLMN_IdentityInfo__ext0O__F2F1_cond.
Opaque PLMN_IdentityInfo__ext0O__cond PLMN_IdentityInfo__ext0O__Format.

Definition PLMN_IdentityInfo__ext0__check_all_none (b : PLMN_IdentityInfo__ext0O__Type) : bool :=
match b with 
  | make__PLMN_IdentityInfo__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PLMN_IdentityInfo__ext0__Format : T_Format PLMN_IdentityInfo__ext0__Type PLMN_IdentityInfo__ext0__cond :=
  restrict_add_format PLMN_IdentityInfo__ext0__check_all_none PLMN_IdentityInfo__ext0O__Format.

Opaque PLMN_IdentityInfo__ext0__cond PLMN_IdentityInfo__ext0__Format.

Definition PLMN_IdentityInfo__ext1O__trackingAreaList_r17__Format : T_Format PLMN_IdentityInfo__ext1O__trackingAreaList_r17__Type PLMN_IdentityInfo__ext1O__trackingAreaList_r17__cond := seq_of_format TrackingAreaCode__Format 1 maxTAC_r17 PLMN_IdentityInfo__ext1O__trackingAreaList_r17__helper1 PLMN_IdentityInfo__ext1O__trackingAreaList_r17__helper2.

Opaque PLMN_IdentityInfo__ext1O__trackingAreaList_r17__cond PLMN_IdentityInfo__ext1O__trackingAreaList_r17__Format.

Definition PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__Format : T_Format Z PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__cond :=
 ranged_int_format (22) (32) PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__helper1 PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__helper2.

Opaque PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__cond PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__Format.


Definition PLMN_IdentityInfo__ext1O__Format_Type := Eval cbn in seq_format_prod PLMN_IdentityInfo__ext1O__list.
Definition PLMN_IdentityInfo__ext1O__Format_list : PLMN_IdentityInfo__ext1O__Format_Type :=
  (PLMN_IdentityInfo__ext1O__trackingAreaList_r17__Format, (PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17__Format, unit_format)).
Definition PLMN_IdentityInfo__ext1O__list__Format := (*Eval compute in *) seq_format PLMN_IdentityInfo__ext1O__list PLMN_IdentityInfo__ext1O__Format_list.
Definition PLMN_IdentityInfo__ext1O__F1 z :=
  (PLMN_IdentityInfo__ext1O__trackingAreaList_r17 z, (PLMN_IdentityInfo__ext1O__gNB_ID_Length_r17 z, tt)).
Definition PLMN_IdentityInfo__ext1O__F2 (y : seq_type PLMN_IdentityInfo__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PLMN_IdentityInfo__ext1O__Type i0 i1
  end.
Lemma PLMN_IdentityInfo__ext1O__F1F2_cond (z : PLMN_IdentityInfo__ext1O__Type)
  : PLMN_IdentityInfo__ext1O__cond z ->
  (seq_cond PLMN_IdentityInfo__ext1O__list (PLMN_IdentityInfo__ext1O__F1 z)).
intro H. unfold PLMN_IdentityInfo__ext1O__cond in H. simpl. auto. Qed.
Lemma PLMN_IdentityInfo__ext1O__F1F2_cond2 (z : PLMN_IdentityInfo__ext1O__Type)
 : PLMN_IdentityInfo__ext1O__F2 (PLMN_IdentityInfo__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PLMN_IdentityInfo__ext1O__F2F1_cond (y : seq_type PLMN_IdentityInfo__ext1O__list)
  : seq_cond PLMN_IdentityInfo__ext1O__list y ->
 (PLMN_IdentityInfo__ext1O__cond (PLMN_IdentityInfo__ext1O__F2 y)) /\  PLMN_IdentityInfo__ext1O__F1 (PLMN_IdentityInfo__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PLMN_IdentityInfo__ext1O__cond. simpl in *. auto.
 - simpl. unfold PLMN_IdentityInfo__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PLMN_IdentityInfo__ext1O__Format : T_Format PLMN_IdentityInfo__ext1O__Type PLMN_IdentityInfo__ext1O__cond :=
        proj2_format  PLMN_IdentityInfo__ext1O__cond PLMN_IdentityInfo__ext1O__list__Format
    PLMN_IdentityInfo__ext1O__F1 PLMN_IdentityInfo__ext1O__F2 PLMN_IdentityInfo__ext1O__F1F2_cond  PLMN_IdentityInfo__ext1O__F1F2_cond2 PLMN_IdentityInfo__ext1O__F2F1_cond.
Opaque PLMN_IdentityInfo__ext1O__cond PLMN_IdentityInfo__ext1O__Format.

Definition PLMN_IdentityInfo__ext1__check_all_none (b : PLMN_IdentityInfo__ext1O__Type) : bool :=
match b with 
  | make__PLMN_IdentityInfo__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition PLMN_IdentityInfo__ext1__Format : T_Format PLMN_IdentityInfo__ext1__Type PLMN_IdentityInfo__ext1__cond :=
  restrict_add_format PLMN_IdentityInfo__ext1__check_all_none PLMN_IdentityInfo__ext1O__Format.

Opaque PLMN_IdentityInfo__ext1__cond PLMN_IdentityInfo__ext1__Format.


Definition PLMN_IdentityInfo__root_Format_Type := Eval cbn in seq_format_prod PLMN_IdentityInfo__root_list.
Definition PLMN_IdentityInfo__root_Format_list : PLMN_IdentityInfo__root_Format_Type :=
  (PLMN_IdentityInfo__plmn_IdentityList__Format, (TrackingAreaCode__Format, (RAN_AreaCode__Format, (CellIdentity__Format, (PLMN_IdentityInfo__cellReservedForOperatorUse__Format, unit_format))))).

Definition PLMN_IdentityInfo__ext_Format_Type := Eval cbn in get_formats PLMN_IdentityInfo__ext_list.
Definition PLMN_IdentityInfo__ext_Format_list : PLMN_IdentityInfo__ext_Format_Type :=
  (PLMN_IdentityInfo__ext0__Format, (PLMN_IdentityInfo__ext1__Format, unit__Format)).

Definition PLMN_IdentityInfo__list_type : Set := (seq_type PLMN_IdentityInfo__root_list) * (seq_ext_type PLMN_IdentityInfo__ext_list).
Definition PLMN_IdentityInfo__list_cond (z : PLMN_IdentityInfo__list_type) : Prop :=
        (seq_cond PLMN_IdentityInfo__root_list (fst z)) /\ (seq_ext_cond PLMN_IdentityInfo__ext_list (snd z)).
Definition PLMN_IdentityInfo__list_format : T_Format PLMN_IdentityInfo__list_type PLMN_IdentityInfo__list_cond :=
 (* Eval compute in *) seq_ext_format PLMN_IdentityInfo__root_list PLMN_IdentityInfo__root_Format_list PLMN_IdentityInfo__ext_list PLMN_IdentityInfo__ext_Format_list.

Opaque PLMN_IdentityInfo__list_format.
Definition PLMN_IdentityInfo__F1 (z : PLMN_IdentityInfo__Type) : PLMN_IdentityInfo__list_type :=
  (((PLMN_IdentityInfo__plmn_IdentityList z, (PLMN_IdentityInfo__trackingAreaCode z, (PLMN_IdentityInfo__ranac z, (PLMN_IdentityInfo__cellIdentity z, (PLMN_IdentityInfo__cellReservedForOperatorUse z, tt)))))), (
(PLMN_IdentityInfo__ext0 z, (PLMN_IdentityInfo__ext1 z, tt)))).
Definition PLMN_IdentityInfo__F2 (y : PLMN_IdentityInfo__list_type) : PLMN_IdentityInfo__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, (i1, _)))=>
    make__PLMN_IdentityInfo__Type j0 j1 j2 j3 j4 i0 i1
  end.
Definition PLMN_IdentityInfo__helper1 : (forall a : PLMN_IdentityInfo__Type, PLMN_IdentityInfo__cond a -> PLMN_IdentityInfo__list_cond (PLMN_IdentityInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PLMN_IdentityInfo__helper2 : (forall a : PLMN_IdentityInfo__Type, PLMN_IdentityInfo__F2 (PLMN_IdentityInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PLMN_IdentityInfo__helper3 : (forall b : PLMN_IdentityInfo__list_type, PLMN_IdentityInfo__list_cond b -> PLMN_IdentityInfo__cond (PLMN_IdentityInfo__F2 b) /\ PLMN_IdentityInfo__F1 (PLMN_IdentityInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PLMN_IdentityInfo__cond, PLMN_IdentityInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PLMN_IdentityInfo__Format : T_Format PLMN_IdentityInfo__Type PLMN_IdentityInfo__cond :=
 proj2_format PLMN_IdentityInfo__cond PLMN_IdentityInfo__list_format  PLMN_IdentityInfo__F1 PLMN_IdentityInfo__F2 PLMN_IdentityInfo__helper1 PLMN_IdentityInfo__helper2 PLMN_IdentityInfo__helper3.

Opaque PLMN_IdentityInfo__cond PLMN_IdentityInfo__Format.

