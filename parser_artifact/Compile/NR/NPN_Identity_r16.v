Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Require Import NR.CAG_IdentityInfo_r16.

Opaque CAG_IdentityInfo_r16__cond CAG_IdentityInfo_r16__Format.

Definition NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type := list CAG_IdentityInfo_r16__Type.

Lemma NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__helper1 : (0 <= 1 <= maxNPN_r16)%Z. unfold maxNPN_r16.
 lia. Qed.
Lemma NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__helper2 : to_bit_sz (Z.to_nat (maxNPN_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNPN_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__cond (z : NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNPN_r16)%Z /\ (list_and CAG_IdentityInfo_r16__cond z) .

Record NPN_Identity_r16__pni_npn_r16__Type : Set :=
  make__NPN_Identity_r16__pni_npn_r16__Type {
    NPN_Identity_r16__pni_npn_r16__plmn_Identity_r16 : PLMN_Identity__Type ;
    NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16 : NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type ;
}.
Definition NPN_Identity_r16__pni_npn_r16__list := (
 Nor PLMN_Identity__Type PLMN_Identity__cond ::
 Nor NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__cond ::
 nil).
Definition NPN_Identity_r16__pni_npn_r16__cond z := 
  PLMN_Identity__cond (NPN_Identity_r16__pni_npn_r16__plmn_Identity_r16 z) /\
  NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__cond (NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16 z) /\
  True.

Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Require Import NR.NID_r16.

Opaque NID_r16__cond NID_r16__Format.

Definition NPN_Identity_r16__snpn_r16__nid_List_r16__Type := list NID_r16__Type.

Lemma NPN_Identity_r16__snpn_r16__nid_List_r16__helper1 : (0 <= 1 <= maxNPN_r16)%Z. unfold maxNPN_r16.
 lia. Qed.
Lemma NPN_Identity_r16__snpn_r16__nid_List_r16__helper2 : to_bit_sz (Z.to_nat (maxNPN_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNPN_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NPN_Identity_r16__snpn_r16__nid_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NPN_Identity_r16__snpn_r16__nid_List_r16__cond (z : NPN_Identity_r16__snpn_r16__nid_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNPN_r16)%Z /\ (list_and NID_r16__cond z) .

Record NPN_Identity_r16__snpn_r16__Type : Set :=
  make__NPN_Identity_r16__snpn_r16__Type {
    NPN_Identity_r16__snpn_r16__plmn_Identity_r16 : PLMN_Identity__Type ;
    NPN_Identity_r16__snpn_r16__nid_List_r16 : NPN_Identity_r16__snpn_r16__nid_List_r16__Type ;
}.
Definition NPN_Identity_r16__snpn_r16__list := (
 Nor PLMN_Identity__Type PLMN_Identity__cond ::
 Nor NPN_Identity_r16__snpn_r16__nid_List_r16__Type NPN_Identity_r16__snpn_r16__nid_List_r16__cond ::
 nil).
Definition NPN_Identity_r16__snpn_r16__cond z := 
  PLMN_Identity__cond (NPN_Identity_r16__snpn_r16__plmn_Identity_r16 z) /\
  NPN_Identity_r16__snpn_r16__nid_List_r16__cond (NPN_Identity_r16__snpn_r16__nid_List_r16 z) /\
  True.


Inductive NPN_Identity_r16__Type : Set :=
  | NPN_Identity_r16__pni_npn_r16 : NPN_Identity_r16__pni_npn_r16__Type -> NPN_Identity_r16__Type
  | NPN_Identity_r16__snpn_r16 : NPN_Identity_r16__snpn_r16__Type -> NPN_Identity_r16__Type
.
Definition NPN_Identity_r16__list : list typ := (
typ_cons NPN_Identity_r16__pni_npn_r16__Type NPN_Identity_r16__pni_npn_r16__cond ::
typ_cons NPN_Identity_r16__snpn_r16__Type NPN_Identity_r16__snpn_r16__cond ::
 nil).
Definition NPN_Identity_r16__cond (c : NPN_Identity_r16__Type) := 
  match c with
  | NPN_Identity_r16__pni_npn_r16 t => NPN_Identity_r16__pni_npn_r16__cond t 
  | NPN_Identity_r16__snpn_r16 t => NPN_Identity_r16__snpn_r16__cond t 
  end.

Lemma NPN_Identity_r16__len_helper1 : to_bit_sz (length NPN_Identity_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NPN_Identity_r16__len_helper2 : 2 <= length2 NPN_Identity_r16__list.
 simpl. lia. Qed.

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
Definition NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Format : T_Format NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Type NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__cond := seq_of_format CAG_IdentityInfo_r16__Format 1 maxNPN_r16 NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__helper1 NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__helper2.

Opaque NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__cond NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Format.


Definition NPN_Identity_r16__pni_npn_r16__Format_Type := Eval cbn in seq_format_prod NPN_Identity_r16__pni_npn_r16__list.
Definition NPN_Identity_r16__pni_npn_r16__Format_list : NPN_Identity_r16__pni_npn_r16__Format_Type :=
  (PLMN_Identity__Format, (NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16__Format, unit_format)).
Definition NPN_Identity_r16__pni_npn_r16__list__Format := (*Eval compute in *) seq_format NPN_Identity_r16__pni_npn_r16__list NPN_Identity_r16__pni_npn_r16__Format_list.
Definition NPN_Identity_r16__pni_npn_r16__F1 z :=
  (NPN_Identity_r16__pni_npn_r16__plmn_Identity_r16 z, (NPN_Identity_r16__pni_npn_r16__cag_IdentityList_r16 z, tt)).
Definition NPN_Identity_r16__pni_npn_r16__F2 (y : seq_type NPN_Identity_r16__pni_npn_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__NPN_Identity_r16__pni_npn_r16__Type i0 i1
  end.
Lemma NPN_Identity_r16__pni_npn_r16__F1F2_cond (z : NPN_Identity_r16__pni_npn_r16__Type)
  : NPN_Identity_r16__pni_npn_r16__cond z ->
  (seq_cond NPN_Identity_r16__pni_npn_r16__list (NPN_Identity_r16__pni_npn_r16__F1 z)).
intro H. unfold NPN_Identity_r16__pni_npn_r16__cond in H. simpl. auto. Qed.
Lemma NPN_Identity_r16__pni_npn_r16__F1F2_cond2 (z : NPN_Identity_r16__pni_npn_r16__Type)
 : NPN_Identity_r16__pni_npn_r16__F2 (NPN_Identity_r16__pni_npn_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NPN_Identity_r16__pni_npn_r16__F2F1_cond (y : seq_type NPN_Identity_r16__pni_npn_r16__list)
  : seq_cond NPN_Identity_r16__pni_npn_r16__list y ->
 (NPN_Identity_r16__pni_npn_r16__cond (NPN_Identity_r16__pni_npn_r16__F2 y)) /\  NPN_Identity_r16__pni_npn_r16__F1 (NPN_Identity_r16__pni_npn_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NPN_Identity_r16__pni_npn_r16__cond. simpl in *. auto.
 - simpl. unfold NPN_Identity_r16__pni_npn_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NPN_Identity_r16__pni_npn_r16__Format : T_Format NPN_Identity_r16__pni_npn_r16__Type NPN_Identity_r16__pni_npn_r16__cond :=
        proj2_format  NPN_Identity_r16__pni_npn_r16__cond NPN_Identity_r16__pni_npn_r16__list__Format
    NPN_Identity_r16__pni_npn_r16__F1 NPN_Identity_r16__pni_npn_r16__F2 NPN_Identity_r16__pni_npn_r16__F1F2_cond  NPN_Identity_r16__pni_npn_r16__F1F2_cond2 NPN_Identity_r16__pni_npn_r16__F2F1_cond.
Opaque NPN_Identity_r16__pni_npn_r16__cond NPN_Identity_r16__pni_npn_r16__Format.

Definition NPN_Identity_r16__snpn_r16__nid_List_r16__Format : T_Format NPN_Identity_r16__snpn_r16__nid_List_r16__Type NPN_Identity_r16__snpn_r16__nid_List_r16__cond := seq_of_format NID_r16__Format 1 maxNPN_r16 NPN_Identity_r16__snpn_r16__nid_List_r16__helper1 NPN_Identity_r16__snpn_r16__nid_List_r16__helper2.

Opaque NPN_Identity_r16__snpn_r16__nid_List_r16__cond NPN_Identity_r16__snpn_r16__nid_List_r16__Format.


Definition NPN_Identity_r16__snpn_r16__Format_Type := Eval cbn in seq_format_prod NPN_Identity_r16__snpn_r16__list.
Definition NPN_Identity_r16__snpn_r16__Format_list : NPN_Identity_r16__snpn_r16__Format_Type :=
  (PLMN_Identity__Format, (NPN_Identity_r16__snpn_r16__nid_List_r16__Format, unit_format)).
Definition NPN_Identity_r16__snpn_r16__list__Format := (*Eval compute in *) seq_format NPN_Identity_r16__snpn_r16__list NPN_Identity_r16__snpn_r16__Format_list.
Definition NPN_Identity_r16__snpn_r16__F1 z :=
  (NPN_Identity_r16__snpn_r16__plmn_Identity_r16 z, (NPN_Identity_r16__snpn_r16__nid_List_r16 z, tt)).
Definition NPN_Identity_r16__snpn_r16__F2 (y : seq_type NPN_Identity_r16__snpn_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__NPN_Identity_r16__snpn_r16__Type i0 i1
  end.
Lemma NPN_Identity_r16__snpn_r16__F1F2_cond (z : NPN_Identity_r16__snpn_r16__Type)
  : NPN_Identity_r16__snpn_r16__cond z ->
  (seq_cond NPN_Identity_r16__snpn_r16__list (NPN_Identity_r16__snpn_r16__F1 z)).
intro H. unfold NPN_Identity_r16__snpn_r16__cond in H. simpl. auto. Qed.
Lemma NPN_Identity_r16__snpn_r16__F1F2_cond2 (z : NPN_Identity_r16__snpn_r16__Type)
 : NPN_Identity_r16__snpn_r16__F2 (NPN_Identity_r16__snpn_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NPN_Identity_r16__snpn_r16__F2F1_cond (y : seq_type NPN_Identity_r16__snpn_r16__list)
  : seq_cond NPN_Identity_r16__snpn_r16__list y ->
 (NPN_Identity_r16__snpn_r16__cond (NPN_Identity_r16__snpn_r16__F2 y)) /\  NPN_Identity_r16__snpn_r16__F1 (NPN_Identity_r16__snpn_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NPN_Identity_r16__snpn_r16__cond. simpl in *. auto.
 - simpl. unfold NPN_Identity_r16__snpn_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NPN_Identity_r16__snpn_r16__Format : T_Format NPN_Identity_r16__snpn_r16__Type NPN_Identity_r16__snpn_r16__cond :=
        proj2_format  NPN_Identity_r16__snpn_r16__cond NPN_Identity_r16__snpn_r16__list__Format
    NPN_Identity_r16__snpn_r16__F1 NPN_Identity_r16__snpn_r16__F2 NPN_Identity_r16__snpn_r16__F1F2_cond  NPN_Identity_r16__snpn_r16__F1F2_cond2 NPN_Identity_r16__snpn_r16__F2F1_cond.
Opaque NPN_Identity_r16__snpn_r16__cond NPN_Identity_r16__snpn_r16__Format.


Definition NPN_Identity_r16__Format_Type := Eval cbn in get_formats NPN_Identity_r16__list.
Definition NPN_Identity_r16__Format_list : NPN_Identity_r16__Format_Type :=
  (NPN_Identity_r16__pni_npn_r16__Format, (NPN_Identity_r16__snpn_r16__Format, unit__Format)).
Definition NPN_Identity_r16__list__Format := Eval compute in choice_format NPN_Identity_r16__list NPN_Identity_r16__len_helper1 NPN_Identity_r16__len_helper2  NPN_Identity_r16__Format_list.
Definition NPN_Identity_r16__F1 (z : NPN_Identity_r16__Type) : (choice NPN_Identity_r16__list) :=
  match z with
   | NPN_Identity_r16__pni_npn_r16 t => existT _ 0 t
  | NPN_Identity_r16__snpn_r16 t => existT _ 1 t
  end.
Definition NPN_Identity_r16__g := (fun n => typ_set (get_nth_typ NPN_Identity_r16__list n)).
Definition NPN_Identity_r16__F2 (y : choice NPN_Identity_r16__list) : NPN_Identity_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NPN_Identity_r16__g n -> NPN_Identity_r16__Type) with
    | 0 => fun (t : NPN_Identity_r16__pni_npn_r16__Type) => NPN_Identity_r16__pni_npn_r16 t 
    | 1 => fun (t : NPN_Identity_r16__snpn_r16__Type) => NPN_Identity_r16__snpn_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : NPN_Identity_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ NPN_Identity_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NPN_Identity_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return NPN_Identity_r16__Type with end) n0
           end t0).

Lemma NPN_Identity_r16__helper2 :  forall (y : NPN_Identity_r16__Type), NPN_Identity_r16__cond y -> choice_cond NPN_Identity_r16__list (NPN_Identity_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NPN_Identity_r16__helper3 :  forall (y : NPN_Identity_r16__Type), NPN_Identity_r16__F2 (NPN_Identity_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NPN_Identity_r16__helper4 : (forall b : choice NPN_Identity_r16__list, choice_cond NPN_Identity_r16__list b -> NPN_Identity_r16__cond (NPN_Identity_r16__F2 b) /\ NPN_Identity_r16__F1 (NPN_Identity_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NPN_Identity_r16__F1 NPN_Identity_r16__F2.
Definition NPN_Identity_r16__Format : T_Format NPN_Identity_r16__Type NPN_Identity_r16__cond :=
  (* Eval compute in *) proj2_format NPN_Identity_r16__cond NPN_Identity_r16__list__Format NPN_Identity_r16__F1 NPN_Identity_r16__F2 NPN_Identity_r16__helper2 NPN_Identity_r16__helper3 NPN_Identity_r16__helper4.
Opaque NPN_Identity_r16__cond NPN_Identity_r16__Format.

