Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NSAG_IdentityInfo_r17.

Opaque NSAG_IdentityInfo_r17__cond NSAG_IdentityInfo_r17__Format.

Require Import NR.CellReselectionPriority.

Opaque CellReselectionPriority__cond CellReselectionPriority__Format.

Require Import NR.CellReselectionSubPriority.

Opaque CellReselectionSubPriority__cond CellReselectionSubPriority__Format.

Require Import NR.SliceCellListNR_r17.

Opaque SliceCellListNR_r17__cond SliceCellListNR_r17__Format.

Require Import NR.SliceCellListNR_r17.

Opaque SliceCellListNR_r17__cond SliceCellListNR_r17__Format.


Inductive SliceInfo_r17__sliceCellListNR_r17__Type : Set :=
  | SliceInfo_r17__sliceCellListNR_r17__sliceAllowedCellListNR_r17 : SliceCellListNR_r17__Type -> SliceInfo_r17__sliceCellListNR_r17__Type
  | SliceInfo_r17__sliceCellListNR_r17__sliceExcludedCellListNR_r17 : SliceCellListNR_r17__Type -> SliceInfo_r17__sliceCellListNR_r17__Type
.
Definition SliceInfo_r17__sliceCellListNR_r17__list : list typ := (
typ_cons SliceCellListNR_r17__Type SliceCellListNR_r17__cond ::
typ_cons SliceCellListNR_r17__Type SliceCellListNR_r17__cond ::
 nil).
Definition SliceInfo_r17__sliceCellListNR_r17__cond (c : SliceInfo_r17__sliceCellListNR_r17__Type) := 
  match c with
  | SliceInfo_r17__sliceCellListNR_r17__sliceAllowedCellListNR_r17 t => SliceCellListNR_r17__cond t 
  | SliceInfo_r17__sliceCellListNR_r17__sliceExcludedCellListNR_r17 t => SliceCellListNR_r17__cond t 
  end.

Lemma SliceInfo_r17__sliceCellListNR_r17__len_helper1 : to_bit_sz (length SliceInfo_r17__sliceCellListNR_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SliceInfo_r17__sliceCellListNR_r17__len_helper2 : 2 <= length2 SliceInfo_r17__sliceCellListNR_r17__list.
 simpl. lia. Qed.
Record SliceInfo_r17__Type : Set :=
  make__SliceInfo_r17__Type {
    SliceInfo_r17__nsag_IdentityInfo_r17 : NSAG_IdentityInfo_r17__Type ;
    SliceInfo_r17__nsag_CellReselectionPriority_r17 : option CellReselectionPriority__Type ;
    SliceInfo_r17__nsag_CellReselectionSubPriority_r17 : option CellReselectionSubPriority__Type ;
    SliceInfo_r17__sliceCellListNR_r17 : option SliceInfo_r17__sliceCellListNR_r17__Type ;
}.
Definition SliceInfo_r17__list := (
 Nor NSAG_IdentityInfo_r17__Type NSAG_IdentityInfo_r17__cond ::
 Opt CellReselectionPriority__Type CellReselectionPriority__cond ::
 Opt CellReselectionSubPriority__Type CellReselectionSubPriority__cond ::
 Opt SliceInfo_r17__sliceCellListNR_r17__Type SliceInfo_r17__sliceCellListNR_r17__cond ::
 nil).
Definition SliceInfo_r17__cond z := 
  NSAG_IdentityInfo_r17__cond (SliceInfo_r17__nsag_IdentityInfo_r17 z) /\
  opt_cond CellReselectionPriority__cond (SliceInfo_r17__nsag_CellReselectionPriority_r17 z) /\
  opt_cond CellReselectionSubPriority__cond (SliceInfo_r17__nsag_CellReselectionSubPriority_r17 z) /\
  opt_cond SliceInfo_r17__sliceCellListNR_r17__cond (SliceInfo_r17__sliceCellListNR_r17 z) /\
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

Definition SliceInfo_r17__sliceCellListNR_r17__Format_Type := Eval cbn in get_formats SliceInfo_r17__sliceCellListNR_r17__list.
Definition SliceInfo_r17__sliceCellListNR_r17__Format_list : SliceInfo_r17__sliceCellListNR_r17__Format_Type :=
  (SliceCellListNR_r17__Format, (SliceCellListNR_r17__Format, unit__Format)).
Definition SliceInfo_r17__sliceCellListNR_r17__list__Format := Eval compute in choice_format SliceInfo_r17__sliceCellListNR_r17__list SliceInfo_r17__sliceCellListNR_r17__len_helper1 SliceInfo_r17__sliceCellListNR_r17__len_helper2  SliceInfo_r17__sliceCellListNR_r17__Format_list.
Definition SliceInfo_r17__sliceCellListNR_r17__F1 (z : SliceInfo_r17__sliceCellListNR_r17__Type) : (choice SliceInfo_r17__sliceCellListNR_r17__list) :=
  match z with
   | SliceInfo_r17__sliceCellListNR_r17__sliceAllowedCellListNR_r17 t => existT _ 0 t
  | SliceInfo_r17__sliceCellListNR_r17__sliceExcludedCellListNR_r17 t => existT _ 1 t
  end.
Definition SliceInfo_r17__sliceCellListNR_r17__g := (fun n => typ_set (get_nth_typ SliceInfo_r17__sliceCellListNR_r17__list n)).
Definition SliceInfo_r17__sliceCellListNR_r17__F2 (y : choice SliceInfo_r17__sliceCellListNR_r17__list) : SliceInfo_r17__sliceCellListNR_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SliceInfo_r17__sliceCellListNR_r17__g n -> SliceInfo_r17__sliceCellListNR_r17__Type) with
    | 0 => fun (t : SliceCellListNR_r17__Type) => SliceInfo_r17__sliceCellListNR_r17__sliceAllowedCellListNR_r17 t 
    | 1 => fun (t : SliceCellListNR_r17__Type) => SliceInfo_r17__sliceCellListNR_r17__sliceExcludedCellListNR_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SliceInfo_r17__sliceCellListNR_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SliceInfo_r17__sliceCellListNR_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SliceInfo_r17__sliceCellListNR_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SliceInfo_r17__sliceCellListNR_r17__Type with end) n0
           end t0).

Lemma SliceInfo_r17__sliceCellListNR_r17__helper2 :  forall (y : SliceInfo_r17__sliceCellListNR_r17__Type), SliceInfo_r17__sliceCellListNR_r17__cond y -> choice_cond SliceInfo_r17__sliceCellListNR_r17__list (SliceInfo_r17__sliceCellListNR_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SliceInfo_r17__sliceCellListNR_r17__helper3 :  forall (y : SliceInfo_r17__sliceCellListNR_r17__Type), SliceInfo_r17__sliceCellListNR_r17__F2 (SliceInfo_r17__sliceCellListNR_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SliceInfo_r17__sliceCellListNR_r17__helper4 : (forall b : choice SliceInfo_r17__sliceCellListNR_r17__list, choice_cond SliceInfo_r17__sliceCellListNR_r17__list b -> SliceInfo_r17__sliceCellListNR_r17__cond (SliceInfo_r17__sliceCellListNR_r17__F2 b) /\ SliceInfo_r17__sliceCellListNR_r17__F1 (SliceInfo_r17__sliceCellListNR_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SliceInfo_r17__sliceCellListNR_r17__F1 SliceInfo_r17__sliceCellListNR_r17__F2.
Definition SliceInfo_r17__sliceCellListNR_r17__Format : T_Format SliceInfo_r17__sliceCellListNR_r17__Type SliceInfo_r17__sliceCellListNR_r17__cond :=
  (* Eval compute in *) proj2_format SliceInfo_r17__sliceCellListNR_r17__cond SliceInfo_r17__sliceCellListNR_r17__list__Format SliceInfo_r17__sliceCellListNR_r17__F1 SliceInfo_r17__sliceCellListNR_r17__F2 SliceInfo_r17__sliceCellListNR_r17__helper2 SliceInfo_r17__sliceCellListNR_r17__helper3 SliceInfo_r17__sliceCellListNR_r17__helper4.
Opaque SliceInfo_r17__sliceCellListNR_r17__cond SliceInfo_r17__sliceCellListNR_r17__Format.


Definition SliceInfo_r17__Format_Type := Eval cbn in seq_format_prod SliceInfo_r17__list.
Definition SliceInfo_r17__Format_list : SliceInfo_r17__Format_Type :=
  (NSAG_IdentityInfo_r17__Format, (CellReselectionPriority__Format, (CellReselectionSubPriority__Format, (SliceInfo_r17__sliceCellListNR_r17__Format, unit_format)))).
Definition SliceInfo_r17__list__Format := (*Eval compute in *) seq_format SliceInfo_r17__list SliceInfo_r17__Format_list.
Definition SliceInfo_r17__F1 z :=
  (SliceInfo_r17__nsag_IdentityInfo_r17 z, (SliceInfo_r17__nsag_CellReselectionPriority_r17 z, (SliceInfo_r17__nsag_CellReselectionSubPriority_r17 z, (SliceInfo_r17__sliceCellListNR_r17 z, tt)))).
Definition SliceInfo_r17__F2 (y : seq_type SliceInfo_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SliceInfo_r17__Type i0 i1 i2 i3
  end.
Lemma SliceInfo_r17__F1F2_cond (z : SliceInfo_r17__Type)
  : SliceInfo_r17__cond z ->
  (seq_cond SliceInfo_r17__list (SliceInfo_r17__F1 z)).
intro H. unfold SliceInfo_r17__cond in H. simpl. auto. Qed.
Lemma SliceInfo_r17__F1F2_cond2 (z : SliceInfo_r17__Type)
 : SliceInfo_r17__F2 (SliceInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SliceInfo_r17__F2F1_cond (y : seq_type SliceInfo_r17__list)
  : seq_cond SliceInfo_r17__list y ->
 (SliceInfo_r17__cond (SliceInfo_r17__F2 y)) /\  SliceInfo_r17__F1 (SliceInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SliceInfo_r17__cond. simpl in *. auto.
 - simpl. unfold SliceInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SliceInfo_r17__Format : T_Format SliceInfo_r17__Type SliceInfo_r17__cond :=
        proj2_format  SliceInfo_r17__cond SliceInfo_r17__list__Format
    SliceInfo_r17__F1 SliceInfo_r17__F2 SliceInfo_r17__F1F2_cond  SliceInfo_r17__F1F2_cond2 SliceInfo_r17__F2F1_cond.
Opaque SliceInfo_r17__cond SliceInfo_r17__Format.

