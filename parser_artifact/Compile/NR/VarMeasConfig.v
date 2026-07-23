Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.MeasIdToAddModList.

Opaque MeasIdToAddModList__cond MeasIdToAddModList__Format.

Require Import NR.MeasObjectToAddModList.

Opaque MeasObjectToAddModList__cond MeasObjectToAddModList__Format.

Require Import NR.ReportConfigToAddModList.

Opaque ReportConfigToAddModList__cond ReportConfigToAddModList__Format.

Require Import NR.QuantityConfig.

Opaque QuantityConfig__cond QuantityConfig__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.


Inductive VarMeasConfig__s_MeasureConfig__Type : Set :=
  | VarMeasConfig__s_MeasureConfig__ssb_RSRP : RSRP_Range__Type -> VarMeasConfig__s_MeasureConfig__Type
  | VarMeasConfig__s_MeasureConfig__csi_RSRP : RSRP_Range__Type -> VarMeasConfig__s_MeasureConfig__Type
.
Definition VarMeasConfig__s_MeasureConfig__list : list typ := (
typ_cons RSRP_Range__Type RSRP_Range__cond ::
typ_cons RSRP_Range__Type RSRP_Range__cond ::
 nil).
Definition VarMeasConfig__s_MeasureConfig__cond (c : VarMeasConfig__s_MeasureConfig__Type) := 
  match c with
  | VarMeasConfig__s_MeasureConfig__ssb_RSRP t => RSRP_Range__cond t 
  | VarMeasConfig__s_MeasureConfig__csi_RSRP t => RSRP_Range__cond t 
  end.

Lemma VarMeasConfig__s_MeasureConfig__len_helper1 : to_bit_sz (length VarMeasConfig__s_MeasureConfig__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma VarMeasConfig__s_MeasureConfig__len_helper2 : 2 <= length2 VarMeasConfig__s_MeasureConfig__list.
 simpl. lia. Qed.
Record VarMeasConfig__Type : Set :=
  make__VarMeasConfig__Type {
    VarMeasConfig__measIdList : option MeasIdToAddModList__Type ;
    VarMeasConfig__measObjectList : option MeasObjectToAddModList__Type ;
    VarMeasConfig__reportConfigList : option ReportConfigToAddModList__Type ;
    VarMeasConfig__quantityConfig : option QuantityConfig__Type ;
    VarMeasConfig__s_MeasureConfig : option VarMeasConfig__s_MeasureConfig__Type ;
}.
Definition VarMeasConfig__list := (
 Opt MeasIdToAddModList__Type MeasIdToAddModList__cond ::
 Opt MeasObjectToAddModList__Type MeasObjectToAddModList__cond ::
 Opt ReportConfigToAddModList__Type ReportConfigToAddModList__cond ::
 Opt QuantityConfig__Type QuantityConfig__cond ::
 Opt VarMeasConfig__s_MeasureConfig__Type VarMeasConfig__s_MeasureConfig__cond ::
 nil).
Definition VarMeasConfig__cond z := 
  opt_cond MeasIdToAddModList__cond (VarMeasConfig__measIdList z) /\
  opt_cond MeasObjectToAddModList__cond (VarMeasConfig__measObjectList z) /\
  opt_cond ReportConfigToAddModList__cond (VarMeasConfig__reportConfigList z) /\
  opt_cond QuantityConfig__cond (VarMeasConfig__quantityConfig z) /\
  opt_cond VarMeasConfig__s_MeasureConfig__cond (VarMeasConfig__s_MeasureConfig z) /\
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

Definition VarMeasConfig__s_MeasureConfig__Format_Type := Eval cbn in get_formats VarMeasConfig__s_MeasureConfig__list.
Definition VarMeasConfig__s_MeasureConfig__Format_list : VarMeasConfig__s_MeasureConfig__Format_Type :=
  (RSRP_Range__Format, (RSRP_Range__Format, unit__Format)).
Definition VarMeasConfig__s_MeasureConfig__list__Format := Eval compute in choice_format VarMeasConfig__s_MeasureConfig__list VarMeasConfig__s_MeasureConfig__len_helper1 VarMeasConfig__s_MeasureConfig__len_helper2  VarMeasConfig__s_MeasureConfig__Format_list.
Definition VarMeasConfig__s_MeasureConfig__F1 (z : VarMeasConfig__s_MeasureConfig__Type) : (choice VarMeasConfig__s_MeasureConfig__list) :=
  match z with
   | VarMeasConfig__s_MeasureConfig__ssb_RSRP t => existT _ 0 t
  | VarMeasConfig__s_MeasureConfig__csi_RSRP t => existT _ 1 t
  end.
Definition VarMeasConfig__s_MeasureConfig__g := (fun n => typ_set (get_nth_typ VarMeasConfig__s_MeasureConfig__list n)).
Definition VarMeasConfig__s_MeasureConfig__F2 (y : choice VarMeasConfig__s_MeasureConfig__list) : VarMeasConfig__s_MeasureConfig__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (VarMeasConfig__s_MeasureConfig__g n -> VarMeasConfig__s_MeasureConfig__Type) with
    | 0 => fun (t : RSRP_Range__Type) => VarMeasConfig__s_MeasureConfig__ssb_RSRP t 
    | 1 => fun (t : RSRP_Range__Type) => VarMeasConfig__s_MeasureConfig__csi_RSRP t 
 | (S (S n0)) => (fun (x' : nat) (t'' : VarMeasConfig__s_MeasureConfig__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ VarMeasConfig__s_MeasureConfig__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len VarMeasConfig__s_MeasureConfig__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return VarMeasConfig__s_MeasureConfig__Type with end) n0
           end t0).

Lemma VarMeasConfig__s_MeasureConfig__helper2 :  forall (y : VarMeasConfig__s_MeasureConfig__Type), VarMeasConfig__s_MeasureConfig__cond y -> choice_cond VarMeasConfig__s_MeasureConfig__list (VarMeasConfig__s_MeasureConfig__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma VarMeasConfig__s_MeasureConfig__helper3 :  forall (y : VarMeasConfig__s_MeasureConfig__Type), VarMeasConfig__s_MeasureConfig__F2 (VarMeasConfig__s_MeasureConfig__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma VarMeasConfig__s_MeasureConfig__helper4 : (forall b : choice VarMeasConfig__s_MeasureConfig__list, choice_cond VarMeasConfig__s_MeasureConfig__list b -> VarMeasConfig__s_MeasureConfig__cond (VarMeasConfig__s_MeasureConfig__F2 b) /\ VarMeasConfig__s_MeasureConfig__F1 (VarMeasConfig__s_MeasureConfig__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length VarMeasConfig__s_MeasureConfig__F1 VarMeasConfig__s_MeasureConfig__F2.
Definition VarMeasConfig__s_MeasureConfig__Format : T_Format VarMeasConfig__s_MeasureConfig__Type VarMeasConfig__s_MeasureConfig__cond :=
  (* Eval compute in *) proj2_format VarMeasConfig__s_MeasureConfig__cond VarMeasConfig__s_MeasureConfig__list__Format VarMeasConfig__s_MeasureConfig__F1 VarMeasConfig__s_MeasureConfig__F2 VarMeasConfig__s_MeasureConfig__helper2 VarMeasConfig__s_MeasureConfig__helper3 VarMeasConfig__s_MeasureConfig__helper4.
Opaque VarMeasConfig__s_MeasureConfig__cond VarMeasConfig__s_MeasureConfig__Format.


Definition VarMeasConfig__Format_Type := Eval cbn in seq_format_prod VarMeasConfig__list.
Definition VarMeasConfig__Format_list : VarMeasConfig__Format_Type :=
  (MeasIdToAddModList__Format, (MeasObjectToAddModList__Format, (ReportConfigToAddModList__Format, (QuantityConfig__Format, (VarMeasConfig__s_MeasureConfig__Format, unit_format))))).
Definition VarMeasConfig__list__Format := (*Eval compute in *) seq_format VarMeasConfig__list VarMeasConfig__Format_list.
Definition VarMeasConfig__F1 z :=
  (VarMeasConfig__measIdList z, (VarMeasConfig__measObjectList z, (VarMeasConfig__reportConfigList z, (VarMeasConfig__quantityConfig z, (VarMeasConfig__s_MeasureConfig z, tt))))).
Definition VarMeasConfig__F2 (y : seq_type VarMeasConfig__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__VarMeasConfig__Type i0 i1 i2 i3 i4
  end.
Lemma VarMeasConfig__F1F2_cond (z : VarMeasConfig__Type)
  : VarMeasConfig__cond z ->
  (seq_cond VarMeasConfig__list (VarMeasConfig__F1 z)).
intro H. unfold VarMeasConfig__cond in H. simpl. auto. Qed.
Lemma VarMeasConfig__F1F2_cond2 (z : VarMeasConfig__Type)
 : VarMeasConfig__F2 (VarMeasConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarMeasConfig__F2F1_cond (y : seq_type VarMeasConfig__list)
  : seq_cond VarMeasConfig__list y ->
 (VarMeasConfig__cond (VarMeasConfig__F2 y)) /\  VarMeasConfig__F1 (VarMeasConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarMeasConfig__cond. simpl in *. auto.
 - simpl. unfold VarMeasConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarMeasConfig__Format : T_Format VarMeasConfig__Type VarMeasConfig__cond :=
        proj2_format  VarMeasConfig__cond VarMeasConfig__list__Format
    VarMeasConfig__F1 VarMeasConfig__F2 VarMeasConfig__F1F2_cond  VarMeasConfig__F1F2_cond2 VarMeasConfig__F2F1_cond.
Opaque VarMeasConfig__cond VarMeasConfig__Format.

