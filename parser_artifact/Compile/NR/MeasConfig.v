Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasObjectToRemoveList.

Opaque MeasObjectToRemoveList__cond MeasObjectToRemoveList__Format.

Require Import NR.MeasObjectToAddModList.

Opaque MeasObjectToAddModList__cond MeasObjectToAddModList__Format.

Require Import NR.ReportConfigToRemoveList.

Opaque ReportConfigToRemoveList__cond ReportConfigToRemoveList__Format.

Require Import NR.ReportConfigToAddModList.

Opaque ReportConfigToAddModList__cond ReportConfigToAddModList__Format.

Require Import NR.MeasIdToRemoveList.

Opaque MeasIdToRemoveList__cond MeasIdToRemoveList__Format.

Require Import NR.MeasIdToAddModList.

Opaque MeasIdToAddModList__cond MeasIdToAddModList__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.


Inductive MeasConfig__s_MeasureConfig__Type : Set :=
  | MeasConfig__s_MeasureConfig__ssb_RSRP : RSRP_Range__Type -> MeasConfig__s_MeasureConfig__Type
  | MeasConfig__s_MeasureConfig__csi_RSRP : RSRP_Range__Type -> MeasConfig__s_MeasureConfig__Type
.
Definition MeasConfig__s_MeasureConfig__list : list typ := (
typ_cons RSRP_Range__Type RSRP_Range__cond ::
typ_cons RSRP_Range__Type RSRP_Range__cond ::
 nil).
Definition MeasConfig__s_MeasureConfig__cond (c : MeasConfig__s_MeasureConfig__Type) := 
  match c with
  | MeasConfig__s_MeasureConfig__ssb_RSRP t => RSRP_Range__cond t 
  | MeasConfig__s_MeasureConfig__csi_RSRP t => RSRP_Range__cond t 
  end.

Lemma MeasConfig__s_MeasureConfig__len_helper1 : to_bit_sz (length MeasConfig__s_MeasureConfig__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasConfig__s_MeasureConfig__len_helper2 : 2 <= length2 MeasConfig__s_MeasureConfig__list.
 simpl. lia. Qed.
Require Import NR.QuantityConfig.

Opaque QuantityConfig__cond QuantityConfig__Format.

Require Import NR.MeasGapConfig.

Opaque MeasGapConfig__cond MeasGapConfig__Format.

Require Import NR.MeasGapSharingConfig.

Opaque MeasGapSharingConfig__cond MeasGapSharingConfig__Format.

Inductive MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Type : Set :=
 | MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__true
.
Definition MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__cond := (fun (_ : MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Type) => True).
Lemma MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__nat__helper.

Definition MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F1 t :=
  match t with
  | MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__true => 0
  end.
Definition MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F2 n :=
  match n with
  | 0 => MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__true
  | _ => MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__true
  end.
Lemma MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F1F2 : forall x : MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Type, (MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F1 x <= 0) /\ MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F2 (MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F2F1 : forall (y : nat) (H : y <= 0), MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F1 (MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F2 y) = y. enum_solve H y. Qed.

Record MeasConfig__ext0O__Type : Set :=
  make__MeasConfig__ext0O__Type {
    MeasConfig__ext0O__interFrequencyConfig_NoGap_r16 : option MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Type ;
}.
Definition MeasConfig__ext0O__list := (
 Opt MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Type MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__cond ::
 nil).
Definition MeasConfig__ext0O__cond z := 
  opt_cond MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__cond (MeasConfig__ext0O__interFrequencyConfig_NoGap_r16 z) /\
  True.

Definition MeasConfig__ext0__Type := MeasConfig__ext0O__Type.
Definition MeasConfig__ext0__cond := MeasConfig__ext0O__cond.

Record MeasConfig__Type : Set :=
  make__MeasConfig__Type {
    MeasConfig__measObjectToRemoveList : option MeasObjectToRemoveList__Type ;
    MeasConfig__measObjectToAddModList : option MeasObjectToAddModList__Type ;
    MeasConfig__reportConfigToRemoveList : option ReportConfigToRemoveList__Type ;
    MeasConfig__reportConfigToAddModList : option ReportConfigToAddModList__Type ;
    MeasConfig__measIdToRemoveList : option MeasIdToRemoveList__Type ;
    MeasConfig__measIdToAddModList : option MeasIdToAddModList__Type ;
    MeasConfig__s_MeasureConfig : option MeasConfig__s_MeasureConfig__Type ;
    MeasConfig__quantityConfig : option QuantityConfig__Type ;
    MeasConfig__measGapConfig : option MeasGapConfig__Type ;
    MeasConfig__measGapSharingConfig : option MeasGapSharingConfig__Type ;
    MeasConfig__ext0 : option MeasConfig__ext0__Type ;
}.
Definition MeasConfig__root_list : list seq_elem := (
 Opt MeasObjectToRemoveList__Type MeasObjectToRemoveList__cond ::
 Opt MeasObjectToAddModList__Type MeasObjectToAddModList__cond ::
 Opt ReportConfigToRemoveList__Type ReportConfigToRemoveList__cond ::
 Opt ReportConfigToAddModList__Type ReportConfigToAddModList__cond ::
 Opt MeasIdToRemoveList__Type MeasIdToRemoveList__cond ::
 Opt MeasIdToAddModList__Type MeasIdToAddModList__cond ::
 Opt MeasConfig__s_MeasureConfig__Type MeasConfig__s_MeasureConfig__cond ::
 Opt QuantityConfig__Type QuantityConfig__cond ::
 Opt MeasGapConfig__Type MeasGapConfig__cond ::
 Opt MeasGapSharingConfig__Type MeasGapSharingConfig__cond ::
 nil).
Definition MeasConfig__ext_list : list typ := (
  typ_cons MeasConfig__ext0__Type MeasConfig__ext0__cond ::
  nil).
Definition MeasConfig__cond (z : MeasConfig__Type) := 
(  opt_cond MeasObjectToRemoveList__cond (MeasConfig__measObjectToRemoveList z) /\
  opt_cond MeasObjectToAddModList__cond (MeasConfig__measObjectToAddModList z) /\
  opt_cond ReportConfigToRemoveList__cond (MeasConfig__reportConfigToRemoveList z) /\
  opt_cond ReportConfigToAddModList__cond (MeasConfig__reportConfigToAddModList z) /\
  opt_cond MeasIdToRemoveList__cond (MeasConfig__measIdToRemoveList z) /\
  opt_cond MeasIdToAddModList__cond (MeasConfig__measIdToAddModList z) /\
  opt_cond MeasConfig__s_MeasureConfig__cond (MeasConfig__s_MeasureConfig z) /\
  opt_cond QuantityConfig__cond (MeasConfig__quantityConfig z) /\
  opt_cond MeasGapConfig__cond (MeasConfig__measGapConfig z) /\
  opt_cond MeasGapSharingConfig__cond (MeasConfig__measGapSharingConfig z) /\
  True) /\ 
(  opt_cond MeasConfig__ext0__cond (MeasConfig__ext0 z) /\
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

Definition MeasConfig__s_MeasureConfig__Format_Type := Eval cbn in get_formats MeasConfig__s_MeasureConfig__list.
Definition MeasConfig__s_MeasureConfig__Format_list : MeasConfig__s_MeasureConfig__Format_Type :=
  (RSRP_Range__Format, (RSRP_Range__Format, unit__Format)).
Definition MeasConfig__s_MeasureConfig__list__Format := Eval compute in choice_format MeasConfig__s_MeasureConfig__list MeasConfig__s_MeasureConfig__len_helper1 MeasConfig__s_MeasureConfig__len_helper2  MeasConfig__s_MeasureConfig__Format_list.
Definition MeasConfig__s_MeasureConfig__F1 (z : MeasConfig__s_MeasureConfig__Type) : (choice MeasConfig__s_MeasureConfig__list) :=
  match z with
   | MeasConfig__s_MeasureConfig__ssb_RSRP t => existT _ 0 t
  | MeasConfig__s_MeasureConfig__csi_RSRP t => existT _ 1 t
  end.
Definition MeasConfig__s_MeasureConfig__g := (fun n => typ_set (get_nth_typ MeasConfig__s_MeasureConfig__list n)).
Definition MeasConfig__s_MeasureConfig__F2 (y : choice MeasConfig__s_MeasureConfig__list) : MeasConfig__s_MeasureConfig__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasConfig__s_MeasureConfig__g n -> MeasConfig__s_MeasureConfig__Type) with
    | 0 => fun (t : RSRP_Range__Type) => MeasConfig__s_MeasureConfig__ssb_RSRP t 
    | 1 => fun (t : RSRP_Range__Type) => MeasConfig__s_MeasureConfig__csi_RSRP t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MeasConfig__s_MeasureConfig__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MeasConfig__s_MeasureConfig__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasConfig__s_MeasureConfig__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MeasConfig__s_MeasureConfig__Type with end) n0
           end t0).

Lemma MeasConfig__s_MeasureConfig__helper2 :  forall (y : MeasConfig__s_MeasureConfig__Type), MeasConfig__s_MeasureConfig__cond y -> choice_cond MeasConfig__s_MeasureConfig__list (MeasConfig__s_MeasureConfig__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasConfig__s_MeasureConfig__helper3 :  forall (y : MeasConfig__s_MeasureConfig__Type), MeasConfig__s_MeasureConfig__F2 (MeasConfig__s_MeasureConfig__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasConfig__s_MeasureConfig__helper4 : (forall b : choice MeasConfig__s_MeasureConfig__list, choice_cond MeasConfig__s_MeasureConfig__list b -> MeasConfig__s_MeasureConfig__cond (MeasConfig__s_MeasureConfig__F2 b) /\ MeasConfig__s_MeasureConfig__F1 (MeasConfig__s_MeasureConfig__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasConfig__s_MeasureConfig__F1 MeasConfig__s_MeasureConfig__F2.
Definition MeasConfig__s_MeasureConfig__Format : T_Format MeasConfig__s_MeasureConfig__Type MeasConfig__s_MeasureConfig__cond :=
  (* Eval compute in *) proj2_format MeasConfig__s_MeasureConfig__cond MeasConfig__s_MeasureConfig__list__Format MeasConfig__s_MeasureConfig__F1 MeasConfig__s_MeasureConfig__F2 MeasConfig__s_MeasureConfig__helper2 MeasConfig__s_MeasureConfig__helper3 MeasConfig__s_MeasureConfig__helper4.
Opaque MeasConfig__s_MeasureConfig__cond MeasConfig__s_MeasureConfig__Format.

Definition MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Format : T_Format MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__nat__Format MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F1 MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F2 MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F1F2 MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__F2F1.

Opaque MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__cond MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Format.


Definition MeasConfig__ext0O__Format_Type := Eval cbn in seq_format_prod MeasConfig__ext0O__list.
Definition MeasConfig__ext0O__Format_list : MeasConfig__ext0O__Format_Type :=
  (MeasConfig__ext0O__interFrequencyConfig_NoGap_r16__Format, unit_format).
Definition MeasConfig__ext0O__list__Format := (*Eval compute in *) seq_format MeasConfig__ext0O__list MeasConfig__ext0O__Format_list.
Definition MeasConfig__ext0O__F1 z :=
  (MeasConfig__ext0O__interFrequencyConfig_NoGap_r16 z, tt).
Definition MeasConfig__ext0O__F2 (y : seq_type MeasConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__MeasConfig__ext0O__Type i0
  end.
Lemma MeasConfig__ext0O__F1F2_cond (z : MeasConfig__ext0O__Type)
  : MeasConfig__ext0O__cond z ->
  (seq_cond MeasConfig__ext0O__list (MeasConfig__ext0O__F1 z)).
intro H. unfold MeasConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasConfig__ext0O__F1F2_cond2 (z : MeasConfig__ext0O__Type)
 : MeasConfig__ext0O__F2 (MeasConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasConfig__ext0O__F2F1_cond (y : seq_type MeasConfig__ext0O__list)
  : seq_cond MeasConfig__ext0O__list y ->
 (MeasConfig__ext0O__cond (MeasConfig__ext0O__F2 y)) /\  MeasConfig__ext0O__F1 (MeasConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasConfig__ext0O__Format : T_Format MeasConfig__ext0O__Type MeasConfig__ext0O__cond :=
        proj2_format  MeasConfig__ext0O__cond MeasConfig__ext0O__list__Format
    MeasConfig__ext0O__F1 MeasConfig__ext0O__F2 MeasConfig__ext0O__F1F2_cond  MeasConfig__ext0O__F1F2_cond2 MeasConfig__ext0O__F2F1_cond.
Opaque MeasConfig__ext0O__cond MeasConfig__ext0O__Format.

Definition MeasConfig__ext0__check_all_none (b : MeasConfig__ext0O__Type) : bool :=
match b with 
  | make__MeasConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition MeasConfig__ext0__Format : T_Format MeasConfig__ext0__Type MeasConfig__ext0__cond :=
  restrict_add_format MeasConfig__ext0__check_all_none MeasConfig__ext0O__Format.

Opaque MeasConfig__ext0__cond MeasConfig__ext0__Format.


Definition MeasConfig__root_Format_Type := Eval cbn in seq_format_prod MeasConfig__root_list.
Definition MeasConfig__root_Format_list : MeasConfig__root_Format_Type :=
  (MeasObjectToRemoveList__Format, (MeasObjectToAddModList__Format, (ReportConfigToRemoveList__Format, (ReportConfigToAddModList__Format, (MeasIdToRemoveList__Format, (MeasIdToAddModList__Format, (MeasConfig__s_MeasureConfig__Format, (QuantityConfig__Format, (MeasGapConfig__Format, (MeasGapSharingConfig__Format, unit_format)))))))))).

Definition MeasConfig__ext_Format_Type := Eval cbn in get_formats MeasConfig__ext_list.
Definition MeasConfig__ext_Format_list : MeasConfig__ext_Format_Type :=
  (MeasConfig__ext0__Format, unit__Format).

Definition MeasConfig__list_type : Set := (seq_type MeasConfig__root_list) * (seq_ext_type MeasConfig__ext_list).
Definition MeasConfig__list_cond (z : MeasConfig__list_type) : Prop :=
        (seq_cond MeasConfig__root_list (fst z)) /\ (seq_ext_cond MeasConfig__ext_list (snd z)).
Definition MeasConfig__list_format : T_Format MeasConfig__list_type MeasConfig__list_cond :=
 (* Eval compute in *) seq_ext_format MeasConfig__root_list MeasConfig__root_Format_list MeasConfig__ext_list MeasConfig__ext_Format_list.

Opaque MeasConfig__list_format.
Definition MeasConfig__F1 (z : MeasConfig__Type) : MeasConfig__list_type :=
  (((MeasConfig__measObjectToRemoveList z, (MeasConfig__measObjectToAddModList z, (MeasConfig__reportConfigToRemoveList z, (MeasConfig__reportConfigToAddModList z, (MeasConfig__measIdToRemoveList z, (MeasConfig__measIdToAddModList z, (MeasConfig__s_MeasureConfig z, (MeasConfig__quantityConfig z, (MeasConfig__measGapConfig z, (MeasConfig__measGapSharingConfig z, tt))))))))))), (
(MeasConfig__ext0 z, tt))).
Definition MeasConfig__F2 (y : MeasConfig__list_type) : MeasConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, _)))))))))), (i0, _))=>
    make__MeasConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i0
  end.
Definition MeasConfig__helper1 : (forall a : MeasConfig__Type, MeasConfig__cond a -> MeasConfig__list_cond (MeasConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasConfig__helper2 : (forall a : MeasConfig__Type, MeasConfig__F2 (MeasConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasConfig__helper3 : (forall b : MeasConfig__list_type, MeasConfig__list_cond b -> MeasConfig__cond (MeasConfig__F2 b) /\ MeasConfig__F1 (MeasConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasConfig__cond, MeasConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasConfig__Format : T_Format MeasConfig__Type MeasConfig__cond :=
 proj2_format MeasConfig__cond MeasConfig__list_format  MeasConfig__F1 MeasConfig__F2 MeasConfig__helper1 MeasConfig__helper2 MeasConfig__helper3.

Opaque MeasConfig__cond MeasConfig__Format.

