Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FeatureSetEUTRA_DownlinkId.

Opaque FeatureSetEUTRA_DownlinkId__cond FeatureSetEUTRA_DownlinkId__Format.

Require Import NR.FeatureSetEUTRA_UplinkId.

Opaque FeatureSetEUTRA_UplinkId__cond FeatureSetEUTRA_UplinkId__Format.

Record FeatureSet__eutra__Type : Set :=
  make__FeatureSet__eutra__Type {
    FeatureSet__eutra__downlinkSetEUTRA : FeatureSetEUTRA_DownlinkId__Type ;
    FeatureSet__eutra__uplinkSetEUTRA : FeatureSetEUTRA_UplinkId__Type ;
}.
Definition FeatureSet__eutra__list := (
 Nor FeatureSetEUTRA_DownlinkId__Type FeatureSetEUTRA_DownlinkId__cond ::
 Nor FeatureSetEUTRA_UplinkId__Type FeatureSetEUTRA_UplinkId__cond ::
 nil).
Definition FeatureSet__eutra__cond z := 
  FeatureSetEUTRA_DownlinkId__cond (FeatureSet__eutra__downlinkSetEUTRA z) /\
  FeatureSetEUTRA_UplinkId__cond (FeatureSet__eutra__uplinkSetEUTRA z) /\
  True.

Require Import NR.FeatureSetDownlinkId.

Opaque FeatureSetDownlinkId__cond FeatureSetDownlinkId__Format.

Require Import NR.FeatureSetUplinkId.

Opaque FeatureSetUplinkId__cond FeatureSetUplinkId__Format.

Record FeatureSet__nr__Type : Set :=
  make__FeatureSet__nr__Type {
    FeatureSet__nr__downlinkSetNR : FeatureSetDownlinkId__Type ;
    FeatureSet__nr__uplinkSetNR : FeatureSetUplinkId__Type ;
}.
Definition FeatureSet__nr__list := (
 Nor FeatureSetDownlinkId__Type FeatureSetDownlinkId__cond ::
 Nor FeatureSetUplinkId__Type FeatureSetUplinkId__cond ::
 nil).
Definition FeatureSet__nr__cond z := 
  FeatureSetDownlinkId__cond (FeatureSet__nr__downlinkSetNR z) /\
  FeatureSetUplinkId__cond (FeatureSet__nr__uplinkSetNR z) /\
  True.


Inductive FeatureSet__Type : Set :=
  | FeatureSet__eutra : FeatureSet__eutra__Type -> FeatureSet__Type
  | FeatureSet__nr : FeatureSet__nr__Type -> FeatureSet__Type
.
Definition FeatureSet__list : list typ := (
typ_cons FeatureSet__eutra__Type FeatureSet__eutra__cond ::
typ_cons FeatureSet__nr__Type FeatureSet__nr__cond ::
 nil).
Definition FeatureSet__cond (c : FeatureSet__Type) := 
  match c with
  | FeatureSet__eutra t => FeatureSet__eutra__cond t 
  | FeatureSet__nr t => FeatureSet__nr__cond t 
  end.

Lemma FeatureSet__len_helper1 : to_bit_sz (length FeatureSet__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma FeatureSet__len_helper2 : 2 <= length2 FeatureSet__list.
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

Definition FeatureSet__eutra__Format_Type := Eval cbn in seq_format_prod FeatureSet__eutra__list.
Definition FeatureSet__eutra__Format_list : FeatureSet__eutra__Format_Type :=
  (FeatureSetEUTRA_DownlinkId__Format, (FeatureSetEUTRA_UplinkId__Format, unit_format)).
Definition FeatureSet__eutra__list__Format := (*Eval compute in *) seq_format FeatureSet__eutra__list FeatureSet__eutra__Format_list.
Definition FeatureSet__eutra__F1 z :=
  (FeatureSet__eutra__downlinkSetEUTRA z, (FeatureSet__eutra__uplinkSetEUTRA z, tt)).
Definition FeatureSet__eutra__F2 (y : seq_type FeatureSet__eutra__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSet__eutra__Type i0 i1
  end.
Lemma FeatureSet__eutra__F1F2_cond (z : FeatureSet__eutra__Type)
  : FeatureSet__eutra__cond z ->
  (seq_cond FeatureSet__eutra__list (FeatureSet__eutra__F1 z)).
intro H. unfold FeatureSet__eutra__cond in H. simpl. auto. Qed.
Lemma FeatureSet__eutra__F1F2_cond2 (z : FeatureSet__eutra__Type)
 : FeatureSet__eutra__F2 (FeatureSet__eutra__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSet__eutra__F2F1_cond (y : seq_type FeatureSet__eutra__list)
  : seq_cond FeatureSet__eutra__list y ->
 (FeatureSet__eutra__cond (FeatureSet__eutra__F2 y)) /\  FeatureSet__eutra__F1 (FeatureSet__eutra__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSet__eutra__cond. simpl in *. auto.
 - simpl. unfold FeatureSet__eutra__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSet__eutra__Format : T_Format FeatureSet__eutra__Type FeatureSet__eutra__cond :=
        proj2_format  FeatureSet__eutra__cond FeatureSet__eutra__list__Format
    FeatureSet__eutra__F1 FeatureSet__eutra__F2 FeatureSet__eutra__F1F2_cond  FeatureSet__eutra__F1F2_cond2 FeatureSet__eutra__F2F1_cond.
Opaque FeatureSet__eutra__cond FeatureSet__eutra__Format.


Definition FeatureSet__nr__Format_Type := Eval cbn in seq_format_prod FeatureSet__nr__list.
Definition FeatureSet__nr__Format_list : FeatureSet__nr__Format_Type :=
  (FeatureSetDownlinkId__Format, (FeatureSetUplinkId__Format, unit_format)).
Definition FeatureSet__nr__list__Format := (*Eval compute in *) seq_format FeatureSet__nr__list FeatureSet__nr__Format_list.
Definition FeatureSet__nr__F1 z :=
  (FeatureSet__nr__downlinkSetNR z, (FeatureSet__nr__uplinkSetNR z, tt)).
Definition FeatureSet__nr__F2 (y : seq_type FeatureSet__nr__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSet__nr__Type i0 i1
  end.
Lemma FeatureSet__nr__F1F2_cond (z : FeatureSet__nr__Type)
  : FeatureSet__nr__cond z ->
  (seq_cond FeatureSet__nr__list (FeatureSet__nr__F1 z)).
intro H. unfold FeatureSet__nr__cond in H. simpl. auto. Qed.
Lemma FeatureSet__nr__F1F2_cond2 (z : FeatureSet__nr__Type)
 : FeatureSet__nr__F2 (FeatureSet__nr__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSet__nr__F2F1_cond (y : seq_type FeatureSet__nr__list)
  : seq_cond FeatureSet__nr__list y ->
 (FeatureSet__nr__cond (FeatureSet__nr__F2 y)) /\  FeatureSet__nr__F1 (FeatureSet__nr__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSet__nr__cond. simpl in *. auto.
 - simpl. unfold FeatureSet__nr__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSet__nr__Format : T_Format FeatureSet__nr__Type FeatureSet__nr__cond :=
        proj2_format  FeatureSet__nr__cond FeatureSet__nr__list__Format
    FeatureSet__nr__F1 FeatureSet__nr__F2 FeatureSet__nr__F1F2_cond  FeatureSet__nr__F1F2_cond2 FeatureSet__nr__F2F1_cond.
Opaque FeatureSet__nr__cond FeatureSet__nr__Format.


Definition FeatureSet__Format_Type := Eval cbn in get_formats FeatureSet__list.
Definition FeatureSet__Format_list : FeatureSet__Format_Type :=
  (FeatureSet__eutra__Format, (FeatureSet__nr__Format, unit__Format)).
Definition FeatureSet__list__Format := Eval compute in choice_format FeatureSet__list FeatureSet__len_helper1 FeatureSet__len_helper2  FeatureSet__Format_list.
Definition FeatureSet__F1 (z : FeatureSet__Type) : (choice FeatureSet__list) :=
  match z with
   | FeatureSet__eutra t => existT _ 0 t
  | FeatureSet__nr t => existT _ 1 t
  end.
Definition FeatureSet__g := (fun n => typ_set (get_nth_typ FeatureSet__list n)).
Definition FeatureSet__F2 (y : choice FeatureSet__list) : FeatureSet__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (FeatureSet__g n -> FeatureSet__Type) with
    | 0 => fun (t : FeatureSet__eutra__Type) => FeatureSet__eutra t 
    | 1 => fun (t : FeatureSet__nr__Type) => FeatureSet__nr t 
 | (S (S n0)) => (fun (x' : nat) (t'' : FeatureSet__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ FeatureSet__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len FeatureSet__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return FeatureSet__Type with end) n0
           end t0).

Lemma FeatureSet__helper2 :  forall (y : FeatureSet__Type), FeatureSet__cond y -> choice_cond FeatureSet__list (FeatureSet__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma FeatureSet__helper3 :  forall (y : FeatureSet__Type), FeatureSet__F2 (FeatureSet__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma FeatureSet__helper4 : (forall b : choice FeatureSet__list, choice_cond FeatureSet__list b -> FeatureSet__cond (FeatureSet__F2 b) /\ FeatureSet__F1 (FeatureSet__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length FeatureSet__F1 FeatureSet__F2.
Definition FeatureSet__Format : T_Format FeatureSet__Type FeatureSet__cond :=
  (* Eval compute in *) proj2_format FeatureSet__cond FeatureSet__list__Format FeatureSet__F1 FeatureSet__F2 FeatureSet__helper2 FeatureSet__helper3 FeatureSet__helper4.
Opaque FeatureSet__cond FeatureSet__Format.

