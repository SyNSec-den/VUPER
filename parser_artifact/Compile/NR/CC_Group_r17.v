Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.DefaultDC_Location_r17.

Opaque DefaultDC_Location_r17__cond DefaultDC_Location_r17__Format.

Require Import NR.OffsetValue_r17.

Opaque OffsetValue_r17__cond OffsetValue_r17__Format.

Require Import NR.OffsetValue_r17.

Opaque OffsetValue_r17__cond OffsetValue_r17__Format.

Definition CC_Group_r17__offsetToDefault_r17__offsetlist__Type := list OffsetValue_r17__Type.

Lemma CC_Group_r17__offsetToDefault_r17__offsetlist__helper1 : (0 <= 1 <= maxNrofReqComDC_Location_r17)%Z. unfold maxNrofReqComDC_Location_r17.
 lia. Qed.
Lemma CC_Group_r17__offsetToDefault_r17__offsetlist__helper2 : to_bit_sz (Z.to_nat (maxNrofReqComDC_Location_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofReqComDC_Location_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CC_Group_r17__offsetToDefault_r17__offsetlist__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CC_Group_r17__offsetToDefault_r17__offsetlist__cond (z : CC_Group_r17__offsetToDefault_r17__offsetlist__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofReqComDC_Location_r17)%Z /\ (list_and OffsetValue_r17__cond z) .


Inductive CC_Group_r17__offsetToDefault_r17__Type : Set :=
  | CC_Group_r17__offsetToDefault_r17__offsetValue : OffsetValue_r17__Type -> CC_Group_r17__offsetToDefault_r17__Type
  | CC_Group_r17__offsetToDefault_r17__offsetlist : CC_Group_r17__offsetToDefault_r17__offsetlist__Type -> CC_Group_r17__offsetToDefault_r17__Type
.
Definition CC_Group_r17__offsetToDefault_r17__list : list typ := (
typ_cons OffsetValue_r17__Type OffsetValue_r17__cond ::
typ_cons CC_Group_r17__offsetToDefault_r17__offsetlist__Type CC_Group_r17__offsetToDefault_r17__offsetlist__cond ::
 nil).
Definition CC_Group_r17__offsetToDefault_r17__cond (c : CC_Group_r17__offsetToDefault_r17__Type) := 
  match c with
  | CC_Group_r17__offsetToDefault_r17__offsetValue t => OffsetValue_r17__cond t 
  | CC_Group_r17__offsetToDefault_r17__offsetlist t => CC_Group_r17__offsetToDefault_r17__offsetlist__cond t 
  end.

Lemma CC_Group_r17__offsetToDefault_r17__len_helper1 : to_bit_sz (length CC_Group_r17__offsetToDefault_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CC_Group_r17__offsetToDefault_r17__len_helper2 : 2 <= length2 CC_Group_r17__offsetToDefault_r17__list.
 simpl. lia. Qed.
Record CC_Group_r17__Type : Set :=
  make__CC_Group_r17__Type {
    CC_Group_r17__servCellIndexLower_r17 : ServCellIndex__Type ;
    CC_Group_r17__servCellIndexHigher_r17 : option ServCellIndex__Type ;
    CC_Group_r17__defaultDC_Location_r17 : DefaultDC_Location_r17__Type ;
    CC_Group_r17__offsetToDefault_r17 : option CC_Group_r17__offsetToDefault_r17__Type ;
}.
Definition CC_Group_r17__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Nor DefaultDC_Location_r17__Type DefaultDC_Location_r17__cond ::
 Opt CC_Group_r17__offsetToDefault_r17__Type CC_Group_r17__offsetToDefault_r17__cond ::
 nil).
Definition CC_Group_r17__cond z := 
  ServCellIndex__cond (CC_Group_r17__servCellIndexLower_r17 z) /\
  opt_cond ServCellIndex__cond (CC_Group_r17__servCellIndexHigher_r17 z) /\
  DefaultDC_Location_r17__cond (CC_Group_r17__defaultDC_Location_r17 z) /\
  opt_cond CC_Group_r17__offsetToDefault_r17__cond (CC_Group_r17__offsetToDefault_r17 z) /\
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
Definition CC_Group_r17__offsetToDefault_r17__offsetlist__Format : T_Format CC_Group_r17__offsetToDefault_r17__offsetlist__Type CC_Group_r17__offsetToDefault_r17__offsetlist__cond := seq_of_format OffsetValue_r17__Format 1 maxNrofReqComDC_Location_r17 CC_Group_r17__offsetToDefault_r17__offsetlist__helper1 CC_Group_r17__offsetToDefault_r17__offsetlist__helper2.

Opaque CC_Group_r17__offsetToDefault_r17__offsetlist__cond CC_Group_r17__offsetToDefault_r17__offsetlist__Format.


Definition CC_Group_r17__offsetToDefault_r17__Format_Type := Eval cbn in get_formats CC_Group_r17__offsetToDefault_r17__list.
Definition CC_Group_r17__offsetToDefault_r17__Format_list : CC_Group_r17__offsetToDefault_r17__Format_Type :=
  (OffsetValue_r17__Format, (CC_Group_r17__offsetToDefault_r17__offsetlist__Format, unit__Format)).
Definition CC_Group_r17__offsetToDefault_r17__list__Format := Eval compute in choice_format CC_Group_r17__offsetToDefault_r17__list CC_Group_r17__offsetToDefault_r17__len_helper1 CC_Group_r17__offsetToDefault_r17__len_helper2  CC_Group_r17__offsetToDefault_r17__Format_list.
Definition CC_Group_r17__offsetToDefault_r17__F1 (z : CC_Group_r17__offsetToDefault_r17__Type) : (choice CC_Group_r17__offsetToDefault_r17__list) :=
  match z with
   | CC_Group_r17__offsetToDefault_r17__offsetValue t => existT _ 0 t
  | CC_Group_r17__offsetToDefault_r17__offsetlist t => existT _ 1 t
  end.
Definition CC_Group_r17__offsetToDefault_r17__g := (fun n => typ_set (get_nth_typ CC_Group_r17__offsetToDefault_r17__list n)).
Definition CC_Group_r17__offsetToDefault_r17__F2 (y : choice CC_Group_r17__offsetToDefault_r17__list) : CC_Group_r17__offsetToDefault_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CC_Group_r17__offsetToDefault_r17__g n -> CC_Group_r17__offsetToDefault_r17__Type) with
    | 0 => fun (t : OffsetValue_r17__Type) => CC_Group_r17__offsetToDefault_r17__offsetValue t 
    | 1 => fun (t : CC_Group_r17__offsetToDefault_r17__offsetlist__Type) => CC_Group_r17__offsetToDefault_r17__offsetlist t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CC_Group_r17__offsetToDefault_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CC_Group_r17__offsetToDefault_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CC_Group_r17__offsetToDefault_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CC_Group_r17__offsetToDefault_r17__Type with end) n0
           end t0).

Lemma CC_Group_r17__offsetToDefault_r17__helper2 :  forall (y : CC_Group_r17__offsetToDefault_r17__Type), CC_Group_r17__offsetToDefault_r17__cond y -> choice_cond CC_Group_r17__offsetToDefault_r17__list (CC_Group_r17__offsetToDefault_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CC_Group_r17__offsetToDefault_r17__helper3 :  forall (y : CC_Group_r17__offsetToDefault_r17__Type), CC_Group_r17__offsetToDefault_r17__F2 (CC_Group_r17__offsetToDefault_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CC_Group_r17__offsetToDefault_r17__helper4 : (forall b : choice CC_Group_r17__offsetToDefault_r17__list, choice_cond CC_Group_r17__offsetToDefault_r17__list b -> CC_Group_r17__offsetToDefault_r17__cond (CC_Group_r17__offsetToDefault_r17__F2 b) /\ CC_Group_r17__offsetToDefault_r17__F1 (CC_Group_r17__offsetToDefault_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CC_Group_r17__offsetToDefault_r17__F1 CC_Group_r17__offsetToDefault_r17__F2.
Definition CC_Group_r17__offsetToDefault_r17__Format : T_Format CC_Group_r17__offsetToDefault_r17__Type CC_Group_r17__offsetToDefault_r17__cond :=
  (* Eval compute in *) proj2_format CC_Group_r17__offsetToDefault_r17__cond CC_Group_r17__offsetToDefault_r17__list__Format CC_Group_r17__offsetToDefault_r17__F1 CC_Group_r17__offsetToDefault_r17__F2 CC_Group_r17__offsetToDefault_r17__helper2 CC_Group_r17__offsetToDefault_r17__helper3 CC_Group_r17__offsetToDefault_r17__helper4.
Opaque CC_Group_r17__offsetToDefault_r17__cond CC_Group_r17__offsetToDefault_r17__Format.


Definition CC_Group_r17__Format_Type := Eval cbn in seq_format_prod CC_Group_r17__list.
Definition CC_Group_r17__Format_list : CC_Group_r17__Format_Type :=
  (ServCellIndex__Format, (ServCellIndex__Format, (DefaultDC_Location_r17__Format, (CC_Group_r17__offsetToDefault_r17__Format, unit_format)))).
Definition CC_Group_r17__list__Format := (*Eval compute in *) seq_format CC_Group_r17__list CC_Group_r17__Format_list.
Definition CC_Group_r17__F1 z :=
  (CC_Group_r17__servCellIndexLower_r17 z, (CC_Group_r17__servCellIndexHigher_r17 z, (CC_Group_r17__defaultDC_Location_r17 z, (CC_Group_r17__offsetToDefault_r17 z, tt)))).
Definition CC_Group_r17__F2 (y : seq_type CC_Group_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CC_Group_r17__Type i0 i1 i2 i3
  end.
Lemma CC_Group_r17__F1F2_cond (z : CC_Group_r17__Type)
  : CC_Group_r17__cond z ->
  (seq_cond CC_Group_r17__list (CC_Group_r17__F1 z)).
intro H. unfold CC_Group_r17__cond in H. simpl. auto. Qed.
Lemma CC_Group_r17__F1F2_cond2 (z : CC_Group_r17__Type)
 : CC_Group_r17__F2 (CC_Group_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CC_Group_r17__F2F1_cond (y : seq_type CC_Group_r17__list)
  : seq_cond CC_Group_r17__list y ->
 (CC_Group_r17__cond (CC_Group_r17__F2 y)) /\  CC_Group_r17__F1 (CC_Group_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CC_Group_r17__cond. simpl in *. auto.
 - simpl. unfold CC_Group_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CC_Group_r17__Format : T_Format CC_Group_r17__Type CC_Group_r17__cond :=
        proj2_format  CC_Group_r17__cond CC_Group_r17__list__Format
    CC_Group_r17__F1 CC_Group_r17__F2 CC_Group_r17__F1F2_cond  CC_Group_r17__F1F2_cond2 CC_Group_r17__F2F1_cond.
Opaque CC_Group_r17__cond CC_Group_r17__Format.

