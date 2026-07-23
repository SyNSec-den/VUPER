Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandIndicatorEUTRA.

Opaque FreqBandIndicatorEUTRA__cond FreqBandIndicatorEUTRA__Format.

Require Import NR.CA_BandwidthClassEUTRA.

Opaque CA_BandwidthClassEUTRA__cond CA_BandwidthClassEUTRA__Format.

Require Import NR.CA_BandwidthClassEUTRA.

Opaque CA_BandwidthClassEUTRA__cond CA_BandwidthClassEUTRA__Format.

Record BandParameters__eutra__Type : Set :=
  make__BandParameters__eutra__Type {
    BandParameters__eutra__bandEUTRA : FreqBandIndicatorEUTRA__Type ;
    BandParameters__eutra__ca_BandwidthClassDL_EUTRA : option CA_BandwidthClassEUTRA__Type ;
    BandParameters__eutra__ca_BandwidthClassUL_EUTRA : option CA_BandwidthClassEUTRA__Type ;
}.
Definition BandParameters__eutra__list := (
 Nor FreqBandIndicatorEUTRA__Type FreqBandIndicatorEUTRA__cond ::
 Opt CA_BandwidthClassEUTRA__Type CA_BandwidthClassEUTRA__cond ::
 Opt CA_BandwidthClassEUTRA__Type CA_BandwidthClassEUTRA__cond ::
 nil).
Definition BandParameters__eutra__cond z := 
  FreqBandIndicatorEUTRA__cond (BandParameters__eutra__bandEUTRA z) /\
  opt_cond CA_BandwidthClassEUTRA__cond (BandParameters__eutra__ca_BandwidthClassDL_EUTRA z) /\
  opt_cond CA_BandwidthClassEUTRA__cond (BandParameters__eutra__ca_BandwidthClassUL_EUTRA z) /\
  True.

Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Require Import NR.CA_BandwidthClassNR.

Opaque CA_BandwidthClassNR__cond CA_BandwidthClassNR__Format.

Require Import NR.CA_BandwidthClassNR.

Opaque CA_BandwidthClassNR__cond CA_BandwidthClassNR__Format.

Record BandParameters__nr__Type : Set :=
  make__BandParameters__nr__Type {
    BandParameters__nr__bandNR : FreqBandIndicatorNR__Type ;
    BandParameters__nr__ca_BandwidthClassDL_NR : option CA_BandwidthClassNR__Type ;
    BandParameters__nr__ca_BandwidthClassUL_NR : option CA_BandwidthClassNR__Type ;
}.
Definition BandParameters__nr__list := (
 Nor FreqBandIndicatorNR__Type FreqBandIndicatorNR__cond ::
 Opt CA_BandwidthClassNR__Type CA_BandwidthClassNR__cond ::
 Opt CA_BandwidthClassNR__Type CA_BandwidthClassNR__cond ::
 nil).
Definition BandParameters__nr__cond z := 
  FreqBandIndicatorNR__cond (BandParameters__nr__bandNR z) /\
  opt_cond CA_BandwidthClassNR__cond (BandParameters__nr__ca_BandwidthClassDL_NR z) /\
  opt_cond CA_BandwidthClassNR__cond (BandParameters__nr__ca_BandwidthClassUL_NR z) /\
  True.


Inductive BandParameters__Type : Set :=
  | BandParameters__eutra : BandParameters__eutra__Type -> BandParameters__Type
  | BandParameters__nr : BandParameters__nr__Type -> BandParameters__Type
.
Definition BandParameters__list : list typ := (
typ_cons BandParameters__eutra__Type BandParameters__eutra__cond ::
typ_cons BandParameters__nr__Type BandParameters__nr__cond ::
 nil).
Definition BandParameters__cond (c : BandParameters__Type) := 
  match c with
  | BandParameters__eutra t => BandParameters__eutra__cond t 
  | BandParameters__nr t => BandParameters__nr__cond t 
  end.

Lemma BandParameters__len_helper1 : to_bit_sz (length BandParameters__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandParameters__len_helper2 : 2 <= length2 BandParameters__list.
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

Definition BandParameters__eutra__Format_Type := Eval cbn in seq_format_prod BandParameters__eutra__list.
Definition BandParameters__eutra__Format_list : BandParameters__eutra__Format_Type :=
  (FreqBandIndicatorEUTRA__Format, (CA_BandwidthClassEUTRA__Format, (CA_BandwidthClassEUTRA__Format, unit_format))).
Definition BandParameters__eutra__list__Format := (*Eval compute in *) seq_format BandParameters__eutra__list BandParameters__eutra__Format_list.
Definition BandParameters__eutra__F1 z :=
  (BandParameters__eutra__bandEUTRA z, (BandParameters__eutra__ca_BandwidthClassDL_EUTRA z, (BandParameters__eutra__ca_BandwidthClassUL_EUTRA z, tt))).
Definition BandParameters__eutra__F2 (y : seq_type BandParameters__eutra__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandParameters__eutra__Type i0 i1 i2
  end.
Lemma BandParameters__eutra__F1F2_cond (z : BandParameters__eutra__Type)
  : BandParameters__eutra__cond z ->
  (seq_cond BandParameters__eutra__list (BandParameters__eutra__F1 z)).
intro H. unfold BandParameters__eutra__cond in H. simpl. auto. Qed.
Lemma BandParameters__eutra__F1F2_cond2 (z : BandParameters__eutra__Type)
 : BandParameters__eutra__F2 (BandParameters__eutra__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters__eutra__F2F1_cond (y : seq_type BandParameters__eutra__list)
  : seq_cond BandParameters__eutra__list y ->
 (BandParameters__eutra__cond (BandParameters__eutra__F2 y)) /\  BandParameters__eutra__F1 (BandParameters__eutra__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters__eutra__cond. simpl in *. auto.
 - simpl. unfold BandParameters__eutra__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters__eutra__Format : T_Format BandParameters__eutra__Type BandParameters__eutra__cond :=
        proj2_format  BandParameters__eutra__cond BandParameters__eutra__list__Format
    BandParameters__eutra__F1 BandParameters__eutra__F2 BandParameters__eutra__F1F2_cond  BandParameters__eutra__F1F2_cond2 BandParameters__eutra__F2F1_cond.
Opaque BandParameters__eutra__cond BandParameters__eutra__Format.


Definition BandParameters__nr__Format_Type := Eval cbn in seq_format_prod BandParameters__nr__list.
Definition BandParameters__nr__Format_list : BandParameters__nr__Format_Type :=
  (FreqBandIndicatorNR__Format, (CA_BandwidthClassNR__Format, (CA_BandwidthClassNR__Format, unit_format))).
Definition BandParameters__nr__list__Format := (*Eval compute in *) seq_format BandParameters__nr__list BandParameters__nr__Format_list.
Definition BandParameters__nr__F1 z :=
  (BandParameters__nr__bandNR z, (BandParameters__nr__ca_BandwidthClassDL_NR z, (BandParameters__nr__ca_BandwidthClassUL_NR z, tt))).
Definition BandParameters__nr__F2 (y : seq_type BandParameters__nr__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandParameters__nr__Type i0 i1 i2
  end.
Lemma BandParameters__nr__F1F2_cond (z : BandParameters__nr__Type)
  : BandParameters__nr__cond z ->
  (seq_cond BandParameters__nr__list (BandParameters__nr__F1 z)).
intro H. unfold BandParameters__nr__cond in H. simpl. auto. Qed.
Lemma BandParameters__nr__F1F2_cond2 (z : BandParameters__nr__Type)
 : BandParameters__nr__F2 (BandParameters__nr__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters__nr__F2F1_cond (y : seq_type BandParameters__nr__list)
  : seq_cond BandParameters__nr__list y ->
 (BandParameters__nr__cond (BandParameters__nr__F2 y)) /\  BandParameters__nr__F1 (BandParameters__nr__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters__nr__cond. simpl in *. auto.
 - simpl. unfold BandParameters__nr__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters__nr__Format : T_Format BandParameters__nr__Type BandParameters__nr__cond :=
        proj2_format  BandParameters__nr__cond BandParameters__nr__list__Format
    BandParameters__nr__F1 BandParameters__nr__F2 BandParameters__nr__F1F2_cond  BandParameters__nr__F1F2_cond2 BandParameters__nr__F2F1_cond.
Opaque BandParameters__nr__cond BandParameters__nr__Format.


Definition BandParameters__Format_Type := Eval cbn in get_formats BandParameters__list.
Definition BandParameters__Format_list : BandParameters__Format_Type :=
  (BandParameters__eutra__Format, (BandParameters__nr__Format, unit__Format)).
Definition BandParameters__list__Format := Eval compute in choice_format BandParameters__list BandParameters__len_helper1 BandParameters__len_helper2  BandParameters__Format_list.
Definition BandParameters__F1 (z : BandParameters__Type) : (choice BandParameters__list) :=
  match z with
   | BandParameters__eutra t => existT _ 0 t
  | BandParameters__nr t => existT _ 1 t
  end.
Definition BandParameters__g := (fun n => typ_set (get_nth_typ BandParameters__list n)).
Definition BandParameters__F2 (y : choice BandParameters__list) : BandParameters__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandParameters__g n -> BandParameters__Type) with
    | 0 => fun (t : BandParameters__eutra__Type) => BandParameters__eutra t 
    | 1 => fun (t : BandParameters__nr__Type) => BandParameters__nr t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandParameters__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandParameters__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandParameters__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandParameters__Type with end) n0
           end t0).

Lemma BandParameters__helper2 :  forall (y : BandParameters__Type), BandParameters__cond y -> choice_cond BandParameters__list (BandParameters__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandParameters__helper3 :  forall (y : BandParameters__Type), BandParameters__F2 (BandParameters__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandParameters__helper4 : (forall b : choice BandParameters__list, choice_cond BandParameters__list b -> BandParameters__cond (BandParameters__F2 b) /\ BandParameters__F1 (BandParameters__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandParameters__F1 BandParameters__F2.
Definition BandParameters__Format : T_Format BandParameters__Type BandParameters__cond :=
  (* Eval compute in *) proj2_format BandParameters__cond BandParameters__list__Format BandParameters__F1 BandParameters__F2 BandParameters__helper2 BandParameters__helper3 BandParameters__helper4.
Opaque BandParameters__cond BandParameters__Format.

