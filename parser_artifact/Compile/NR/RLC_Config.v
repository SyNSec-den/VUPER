Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UL_AM_RLC.

Opaque UL_AM_RLC__cond UL_AM_RLC__Format.

Require Import NR.DL_AM_RLC.

Opaque DL_AM_RLC__cond DL_AM_RLC__Format.

Record RLC_Config__root__am__Type : Set :=
  make__RLC_Config__root__am__Type {
    RLC_Config__root__am__ul_AM_RLC : UL_AM_RLC__Type ;
    RLC_Config__root__am__dl_AM_RLC : DL_AM_RLC__Type ;
}.
Definition RLC_Config__root__am__list := (
 Nor UL_AM_RLC__Type UL_AM_RLC__cond ::
 Nor DL_AM_RLC__Type DL_AM_RLC__cond ::
 nil).
Definition RLC_Config__root__am__cond z := 
  UL_AM_RLC__cond (RLC_Config__root__am__ul_AM_RLC z) /\
  DL_AM_RLC__cond (RLC_Config__root__am__dl_AM_RLC z) /\
  True.

Require Import NR.UL_UM_RLC.

Opaque UL_UM_RLC__cond UL_UM_RLC__Format.

Require Import NR.DL_UM_RLC.

Opaque DL_UM_RLC__cond DL_UM_RLC__Format.

Record RLC_Config__root__um_Bi_Directional__Type : Set :=
  make__RLC_Config__root__um_Bi_Directional__Type {
    RLC_Config__root__um_Bi_Directional__ul_UM_RLC : UL_UM_RLC__Type ;
    RLC_Config__root__um_Bi_Directional__dl_UM_RLC : DL_UM_RLC__Type ;
}.
Definition RLC_Config__root__um_Bi_Directional__list := (
 Nor UL_UM_RLC__Type UL_UM_RLC__cond ::
 Nor DL_UM_RLC__Type DL_UM_RLC__cond ::
 nil).
Definition RLC_Config__root__um_Bi_Directional__cond z := 
  UL_UM_RLC__cond (RLC_Config__root__um_Bi_Directional__ul_UM_RLC z) /\
  DL_UM_RLC__cond (RLC_Config__root__um_Bi_Directional__dl_UM_RLC z) /\
  True.

Require Import NR.UL_UM_RLC.

Opaque UL_UM_RLC__cond UL_UM_RLC__Format.

Record RLC_Config__root__um_Uni_Directional_UL__Type : Set :=
  make__RLC_Config__root__um_Uni_Directional_UL__Type {
    RLC_Config__root__um_Uni_Directional_UL__ul_UM_RLC : UL_UM_RLC__Type ;
}.
Definition RLC_Config__root__um_Uni_Directional_UL__list := (
 Nor UL_UM_RLC__Type UL_UM_RLC__cond ::
 nil).
Definition RLC_Config__root__um_Uni_Directional_UL__cond z := 
  UL_UM_RLC__cond (RLC_Config__root__um_Uni_Directional_UL__ul_UM_RLC z) /\
  True.

Require Import NR.DL_UM_RLC.

Opaque DL_UM_RLC__cond DL_UM_RLC__Format.

Record RLC_Config__root__um_Uni_Directional_DL__Type : Set :=
  make__RLC_Config__root__um_Uni_Directional_DL__Type {
    RLC_Config__root__um_Uni_Directional_DL__dl_UM_RLC : DL_UM_RLC__Type ;
}.
Definition RLC_Config__root__um_Uni_Directional_DL__list := (
 Nor DL_UM_RLC__Type DL_UM_RLC__cond ::
 nil).
Definition RLC_Config__root__um_Uni_Directional_DL__cond z := 
  DL_UM_RLC__cond (RLC_Config__root__um_Uni_Directional_DL__dl_UM_RLC z) /\
  True.


Inductive RLC_Config__root__Type : Set :=
  | RLC_Config__root__am : RLC_Config__root__am__Type -> RLC_Config__root__Type
  | RLC_Config__root__um_Bi_Directional : RLC_Config__root__um_Bi_Directional__Type -> RLC_Config__root__Type
  | RLC_Config__root__um_Uni_Directional_UL : RLC_Config__root__um_Uni_Directional_UL__Type -> RLC_Config__root__Type
  | RLC_Config__root__um_Uni_Directional_DL : RLC_Config__root__um_Uni_Directional_DL__Type -> RLC_Config__root__Type
.
Definition RLC_Config__root__list : list typ := (
typ_cons RLC_Config__root__am__Type RLC_Config__root__am__cond ::
typ_cons RLC_Config__root__um_Bi_Directional__Type RLC_Config__root__um_Bi_Directional__cond ::
typ_cons RLC_Config__root__um_Uni_Directional_UL__Type RLC_Config__root__um_Uni_Directional_UL__cond ::
typ_cons RLC_Config__root__um_Uni_Directional_DL__Type RLC_Config__root__um_Uni_Directional_DL__cond ::
 nil).
Definition RLC_Config__root__cond (c : RLC_Config__root__Type) := 
  match c with
  | RLC_Config__root__am t => RLC_Config__root__am__cond t 
  | RLC_Config__root__um_Bi_Directional t => RLC_Config__root__um_Bi_Directional__cond t 
  | RLC_Config__root__um_Uni_Directional_UL t => RLC_Config__root__um_Uni_Directional_UL__cond t 
  | RLC_Config__root__um_Uni_Directional_DL t => RLC_Config__root__um_Uni_Directional_DL__cond t 
  end.

Lemma RLC_Config__root__len_helper1 : to_bit_sz (length RLC_Config__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLC_Config__root__len_helper2 : 2 <= length2 RLC_Config__root__list.
 simpl. lia. Qed.

Definition RLC_Config__ext__Type : Set := Empty_set.
Definition RLC_Config__ext__cond (c : RLC_Config__ext__Type) := True.
Definition RLC_Config__Type : Set := RLC_Config__root__Type + RLC_Config__ext__Type.
Definition RLC_Config__cond :=
  sum_cond RLC_Config__root__cond RLC_Config__ext__cond.

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

Definition RLC_Config__root__am__Format_Type := Eval cbn in seq_format_prod RLC_Config__root__am__list.
Definition RLC_Config__root__am__Format_list : RLC_Config__root__am__Format_Type :=
  (UL_AM_RLC__Format, (DL_AM_RLC__Format, unit_format)).
Definition RLC_Config__root__am__list__Format := (*Eval compute in *) seq_format RLC_Config__root__am__list RLC_Config__root__am__Format_list.
Definition RLC_Config__root__am__F1 z :=
  (RLC_Config__root__am__ul_AM_RLC z, (RLC_Config__root__am__dl_AM_RLC z, tt)).
Definition RLC_Config__root__am__F2 (y : seq_type RLC_Config__root__am__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RLC_Config__root__am__Type i0 i1
  end.
Lemma RLC_Config__root__am__F1F2_cond (z : RLC_Config__root__am__Type)
  : RLC_Config__root__am__cond z ->
  (seq_cond RLC_Config__root__am__list (RLC_Config__root__am__F1 z)).
intro H. unfold RLC_Config__root__am__cond in H. simpl. auto. Qed.
Lemma RLC_Config__root__am__F1F2_cond2 (z : RLC_Config__root__am__Type)
 : RLC_Config__root__am__F2 (RLC_Config__root__am__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLC_Config__root__am__F2F1_cond (y : seq_type RLC_Config__root__am__list)
  : seq_cond RLC_Config__root__am__list y ->
 (RLC_Config__root__am__cond (RLC_Config__root__am__F2 y)) /\  RLC_Config__root__am__F1 (RLC_Config__root__am__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLC_Config__root__am__cond. simpl in *. auto.
 - simpl. unfold RLC_Config__root__am__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLC_Config__root__am__Format : T_Format RLC_Config__root__am__Type RLC_Config__root__am__cond :=
        proj2_format  RLC_Config__root__am__cond RLC_Config__root__am__list__Format
    RLC_Config__root__am__F1 RLC_Config__root__am__F2 RLC_Config__root__am__F1F2_cond  RLC_Config__root__am__F1F2_cond2 RLC_Config__root__am__F2F1_cond.
Opaque RLC_Config__root__am__cond RLC_Config__root__am__Format.


Definition RLC_Config__root__um_Bi_Directional__Format_Type := Eval cbn in seq_format_prod RLC_Config__root__um_Bi_Directional__list.
Definition RLC_Config__root__um_Bi_Directional__Format_list : RLC_Config__root__um_Bi_Directional__Format_Type :=
  (UL_UM_RLC__Format, (DL_UM_RLC__Format, unit_format)).
Definition RLC_Config__root__um_Bi_Directional__list__Format := (*Eval compute in *) seq_format RLC_Config__root__um_Bi_Directional__list RLC_Config__root__um_Bi_Directional__Format_list.
Definition RLC_Config__root__um_Bi_Directional__F1 z :=
  (RLC_Config__root__um_Bi_Directional__ul_UM_RLC z, (RLC_Config__root__um_Bi_Directional__dl_UM_RLC z, tt)).
Definition RLC_Config__root__um_Bi_Directional__F2 (y : seq_type RLC_Config__root__um_Bi_Directional__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RLC_Config__root__um_Bi_Directional__Type i0 i1
  end.
Lemma RLC_Config__root__um_Bi_Directional__F1F2_cond (z : RLC_Config__root__um_Bi_Directional__Type)
  : RLC_Config__root__um_Bi_Directional__cond z ->
  (seq_cond RLC_Config__root__um_Bi_Directional__list (RLC_Config__root__um_Bi_Directional__F1 z)).
intro H. unfold RLC_Config__root__um_Bi_Directional__cond in H. simpl. auto. Qed.
Lemma RLC_Config__root__um_Bi_Directional__F1F2_cond2 (z : RLC_Config__root__um_Bi_Directional__Type)
 : RLC_Config__root__um_Bi_Directional__F2 (RLC_Config__root__um_Bi_Directional__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLC_Config__root__um_Bi_Directional__F2F1_cond (y : seq_type RLC_Config__root__um_Bi_Directional__list)
  : seq_cond RLC_Config__root__um_Bi_Directional__list y ->
 (RLC_Config__root__um_Bi_Directional__cond (RLC_Config__root__um_Bi_Directional__F2 y)) /\  RLC_Config__root__um_Bi_Directional__F1 (RLC_Config__root__um_Bi_Directional__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLC_Config__root__um_Bi_Directional__cond. simpl in *. auto.
 - simpl. unfold RLC_Config__root__um_Bi_Directional__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLC_Config__root__um_Bi_Directional__Format : T_Format RLC_Config__root__um_Bi_Directional__Type RLC_Config__root__um_Bi_Directional__cond :=
        proj2_format  RLC_Config__root__um_Bi_Directional__cond RLC_Config__root__um_Bi_Directional__list__Format
    RLC_Config__root__um_Bi_Directional__F1 RLC_Config__root__um_Bi_Directional__F2 RLC_Config__root__um_Bi_Directional__F1F2_cond  RLC_Config__root__um_Bi_Directional__F1F2_cond2 RLC_Config__root__um_Bi_Directional__F2F1_cond.
Opaque RLC_Config__root__um_Bi_Directional__cond RLC_Config__root__um_Bi_Directional__Format.


Definition RLC_Config__root__um_Uni_Directional_UL__Format_Type := Eval cbn in seq_format_prod RLC_Config__root__um_Uni_Directional_UL__list.
Definition RLC_Config__root__um_Uni_Directional_UL__Format_list : RLC_Config__root__um_Uni_Directional_UL__Format_Type :=
  (UL_UM_RLC__Format, unit_format).
Definition RLC_Config__root__um_Uni_Directional_UL__list__Format := (*Eval compute in *) seq_format RLC_Config__root__um_Uni_Directional_UL__list RLC_Config__root__um_Uni_Directional_UL__Format_list.
Definition RLC_Config__root__um_Uni_Directional_UL__F1 z :=
  (RLC_Config__root__um_Uni_Directional_UL__ul_UM_RLC z, tt).
Definition RLC_Config__root__um_Uni_Directional_UL__F2 (y : seq_type RLC_Config__root__um_Uni_Directional_UL__list) :=
  match y with
  | (i0, _)=>
    make__RLC_Config__root__um_Uni_Directional_UL__Type i0
  end.
Lemma RLC_Config__root__um_Uni_Directional_UL__F1F2_cond (z : RLC_Config__root__um_Uni_Directional_UL__Type)
  : RLC_Config__root__um_Uni_Directional_UL__cond z ->
  (seq_cond RLC_Config__root__um_Uni_Directional_UL__list (RLC_Config__root__um_Uni_Directional_UL__F1 z)).
intro H. unfold RLC_Config__root__um_Uni_Directional_UL__cond in H. simpl. auto. Qed.
Lemma RLC_Config__root__um_Uni_Directional_UL__F1F2_cond2 (z : RLC_Config__root__um_Uni_Directional_UL__Type)
 : RLC_Config__root__um_Uni_Directional_UL__F2 (RLC_Config__root__um_Uni_Directional_UL__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLC_Config__root__um_Uni_Directional_UL__F2F1_cond (y : seq_type RLC_Config__root__um_Uni_Directional_UL__list)
  : seq_cond RLC_Config__root__um_Uni_Directional_UL__list y ->
 (RLC_Config__root__um_Uni_Directional_UL__cond (RLC_Config__root__um_Uni_Directional_UL__F2 y)) /\  RLC_Config__root__um_Uni_Directional_UL__F1 (RLC_Config__root__um_Uni_Directional_UL__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLC_Config__root__um_Uni_Directional_UL__cond. simpl in *. auto.
 - simpl. unfold RLC_Config__root__um_Uni_Directional_UL__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLC_Config__root__um_Uni_Directional_UL__Format : T_Format RLC_Config__root__um_Uni_Directional_UL__Type RLC_Config__root__um_Uni_Directional_UL__cond :=
        proj2_format  RLC_Config__root__um_Uni_Directional_UL__cond RLC_Config__root__um_Uni_Directional_UL__list__Format
    RLC_Config__root__um_Uni_Directional_UL__F1 RLC_Config__root__um_Uni_Directional_UL__F2 RLC_Config__root__um_Uni_Directional_UL__F1F2_cond  RLC_Config__root__um_Uni_Directional_UL__F1F2_cond2 RLC_Config__root__um_Uni_Directional_UL__F2F1_cond.
Opaque RLC_Config__root__um_Uni_Directional_UL__cond RLC_Config__root__um_Uni_Directional_UL__Format.


Definition RLC_Config__root__um_Uni_Directional_DL__Format_Type := Eval cbn in seq_format_prod RLC_Config__root__um_Uni_Directional_DL__list.
Definition RLC_Config__root__um_Uni_Directional_DL__Format_list : RLC_Config__root__um_Uni_Directional_DL__Format_Type :=
  (DL_UM_RLC__Format, unit_format).
Definition RLC_Config__root__um_Uni_Directional_DL__list__Format := (*Eval compute in *) seq_format RLC_Config__root__um_Uni_Directional_DL__list RLC_Config__root__um_Uni_Directional_DL__Format_list.
Definition RLC_Config__root__um_Uni_Directional_DL__F1 z :=
  (RLC_Config__root__um_Uni_Directional_DL__dl_UM_RLC z, tt).
Definition RLC_Config__root__um_Uni_Directional_DL__F2 (y : seq_type RLC_Config__root__um_Uni_Directional_DL__list) :=
  match y with
  | (i0, _)=>
    make__RLC_Config__root__um_Uni_Directional_DL__Type i0
  end.
Lemma RLC_Config__root__um_Uni_Directional_DL__F1F2_cond (z : RLC_Config__root__um_Uni_Directional_DL__Type)
  : RLC_Config__root__um_Uni_Directional_DL__cond z ->
  (seq_cond RLC_Config__root__um_Uni_Directional_DL__list (RLC_Config__root__um_Uni_Directional_DL__F1 z)).
intro H. unfold RLC_Config__root__um_Uni_Directional_DL__cond in H. simpl. auto. Qed.
Lemma RLC_Config__root__um_Uni_Directional_DL__F1F2_cond2 (z : RLC_Config__root__um_Uni_Directional_DL__Type)
 : RLC_Config__root__um_Uni_Directional_DL__F2 (RLC_Config__root__um_Uni_Directional_DL__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLC_Config__root__um_Uni_Directional_DL__F2F1_cond (y : seq_type RLC_Config__root__um_Uni_Directional_DL__list)
  : seq_cond RLC_Config__root__um_Uni_Directional_DL__list y ->
 (RLC_Config__root__um_Uni_Directional_DL__cond (RLC_Config__root__um_Uni_Directional_DL__F2 y)) /\  RLC_Config__root__um_Uni_Directional_DL__F1 (RLC_Config__root__um_Uni_Directional_DL__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLC_Config__root__um_Uni_Directional_DL__cond. simpl in *. auto.
 - simpl. unfold RLC_Config__root__um_Uni_Directional_DL__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLC_Config__root__um_Uni_Directional_DL__Format : T_Format RLC_Config__root__um_Uni_Directional_DL__Type RLC_Config__root__um_Uni_Directional_DL__cond :=
        proj2_format  RLC_Config__root__um_Uni_Directional_DL__cond RLC_Config__root__um_Uni_Directional_DL__list__Format
    RLC_Config__root__um_Uni_Directional_DL__F1 RLC_Config__root__um_Uni_Directional_DL__F2 RLC_Config__root__um_Uni_Directional_DL__F1F2_cond  RLC_Config__root__um_Uni_Directional_DL__F1F2_cond2 RLC_Config__root__um_Uni_Directional_DL__F2F1_cond.
Opaque RLC_Config__root__um_Uni_Directional_DL__cond RLC_Config__root__um_Uni_Directional_DL__Format.


Definition RLC_Config__root__Format_Type := Eval cbn in get_formats RLC_Config__root__list.
Definition RLC_Config__root__Format_list : RLC_Config__root__Format_Type :=
  (RLC_Config__root__am__Format, (RLC_Config__root__um_Bi_Directional__Format, (RLC_Config__root__um_Uni_Directional_UL__Format, (RLC_Config__root__um_Uni_Directional_DL__Format, unit__Format)))).
Definition RLC_Config__root__list__Format := Eval compute in choice_format RLC_Config__root__list RLC_Config__root__len_helper1 RLC_Config__root__len_helper2  RLC_Config__root__Format_list.
Definition RLC_Config__root__F1 (z : RLC_Config__root__Type) : (choice RLC_Config__root__list) :=
  match z with
   | RLC_Config__root__am t => existT _ 0 t
  | RLC_Config__root__um_Bi_Directional t => existT _ 1 t
  | RLC_Config__root__um_Uni_Directional_UL t => existT _ 2 t
  | RLC_Config__root__um_Uni_Directional_DL t => existT _ 3 t
  end.
Definition RLC_Config__root__g := (fun n => typ_set (get_nth_typ RLC_Config__root__list n)).
Definition RLC_Config__root__F2 (y : choice RLC_Config__root__list) : RLC_Config__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLC_Config__root__g n -> RLC_Config__root__Type) with
    | 0 => fun (t : RLC_Config__root__am__Type) => RLC_Config__root__am t 
    | 1 => fun (t : RLC_Config__root__um_Bi_Directional__Type) => RLC_Config__root__um_Bi_Directional t 
    | 2 => fun (t : RLC_Config__root__um_Uni_Directional_UL__Type) => RLC_Config__root__um_Uni_Directional_UL t 
    | 3 => fun (t : RLC_Config__root__um_Uni_Directional_DL__Type) => RLC_Config__root__um_Uni_Directional_DL t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : RLC_Config__root__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ RLC_Config__root__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLC_Config__root__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return RLC_Config__root__Type with end) n0
           end t0).

Lemma RLC_Config__root__helper2 :  forall (y : RLC_Config__root__Type), RLC_Config__root__cond y -> choice_cond RLC_Config__root__list (RLC_Config__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLC_Config__root__helper3 :  forall (y : RLC_Config__root__Type), RLC_Config__root__F2 (RLC_Config__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLC_Config__root__helper4 : (forall b : choice RLC_Config__root__list, choice_cond RLC_Config__root__list b -> RLC_Config__root__cond (RLC_Config__root__F2 b) /\ RLC_Config__root__F1 (RLC_Config__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLC_Config__root__F1 RLC_Config__root__F2.
Definition RLC_Config__root__Format : T_Format RLC_Config__root__Type RLC_Config__root__cond :=
  (* Eval compute in *) proj2_format RLC_Config__root__cond RLC_Config__root__list__Format RLC_Config__root__F1 RLC_Config__root__F2 RLC_Config__root__helper2 RLC_Config__root__helper3 RLC_Config__root__helper4.
Opaque RLC_Config__root__cond RLC_Config__root__Format.

Definition RLC_Config__ext__Format : T_Format RLC_Config__ext__Type RLC_Config__ext__cond := empty_format.
Opaque RLC_Config__ext__cond RLC_Config__ext__Format.

Definition RLC_Config__Format : T_Format RLC_Config__Type RLC_Config__cond := sum_format RLC_Config__root__Format RLC_Config__ext__Format.
Opaque RLC_Config__cond RLC_Config__Format.

