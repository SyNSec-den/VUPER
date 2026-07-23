Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SCellIndex.

Opaque SCellIndex__cond SCellIndex__Format.

Require Import NR.ServingCellConfigCommon.

Opaque ServingCellConfigCommon__cond ServingCellConfigCommon__Format.

Require Import NR.ServingCellConfig.

Opaque ServingCellConfig__cond ServingCellConfig__Format.

Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Record SCellConfig__ext0O__Type : Set :=
  make__SCellConfig__ext0O__Type {
    SCellConfig__ext0O__smtc : option SSB_MTC__Type ;
}.
Definition SCellConfig__ext0O__list := (
 Opt SSB_MTC__Type SSB_MTC__cond ::
 nil).
Definition SCellConfig__ext0O__cond z := 
  opt_cond SSB_MTC__cond (SCellConfig__ext0O__smtc z) /\
  True.

Definition SCellConfig__ext0__Type := SCellConfig__ext0O__Type.
Definition SCellConfig__ext0__cond := SCellConfig__ext0O__cond.

Inductive SCellConfig__ext1O__sCellState_r16__Type : Set :=
 | SCellConfig__ext1O__sCellState_r16__activated
.
Definition SCellConfig__ext1O__sCellState_r16__cond := (fun (_ : SCellConfig__ext1O__sCellState_r16__Type) => True).
Lemma SCellConfig__ext1O__sCellState_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SCellConfig__ext1O__sCellState_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SCellConfig__ext1O__sCellState_r16__nat__helper.

Definition SCellConfig__ext1O__sCellState_r16__F1 t :=
  match t with
  | SCellConfig__ext1O__sCellState_r16__activated => 0
  end.
Definition SCellConfig__ext1O__sCellState_r16__F2 n :=
  match n with
  | 0 => SCellConfig__ext1O__sCellState_r16__activated
  | _ => SCellConfig__ext1O__sCellState_r16__activated
  end.
Lemma SCellConfig__ext1O__sCellState_r16__F1F2 : forall x : SCellConfig__ext1O__sCellState_r16__Type, (SCellConfig__ext1O__sCellState_r16__F1 x <= 0) /\ SCellConfig__ext1O__sCellState_r16__F2 (SCellConfig__ext1O__sCellState_r16__F1 x) = x. imp_solve. Qed.
Lemma SCellConfig__ext1O__sCellState_r16__F2F1 : forall (y : nat) (H : y <= 0), SCellConfig__ext1O__sCellState_r16__F1 (SCellConfig__ext1O__sCellState_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Type : Set :=
 | SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__true
.
Definition SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__cond := (fun (_ : SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Type) => True).
Lemma SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__nat__helper.

Definition SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F1 t :=
  match t with
  | SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__true => 0
  end.
Definition SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F2 n :=
  match n with
  | 0 => SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__true
  | _ => SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__true
  end.
Lemma SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F1F2 : forall x : SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Type, (SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F1 x <= 0) /\ SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F2 (SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F1 x) = x. imp_solve. Qed.
Lemma SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F2F1 : forall (y : nat) (H : y <= 0), SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F1 (SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F2 y) = y. enum_solve H y. Qed.

Record SCellConfig__ext1O__Type : Set :=
  make__SCellConfig__ext1O__Type {
    SCellConfig__ext1O__sCellState_r16 : option SCellConfig__ext1O__sCellState_r16__Type ;
    SCellConfig__ext1O__secondaryDRX_GroupConfig_r16 : option SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Type ;
}.
Definition SCellConfig__ext1O__list := (
 Opt SCellConfig__ext1O__sCellState_r16__Type SCellConfig__ext1O__sCellState_r16__cond ::
 Opt SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Type SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__cond ::
 nil).
Definition SCellConfig__ext1O__cond z := 
  opt_cond SCellConfig__ext1O__sCellState_r16__cond (SCellConfig__ext1O__sCellState_r16 z) /\
  opt_cond SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__cond (SCellConfig__ext1O__secondaryDRX_GroupConfig_r16 z) /\
  True.

Definition SCellConfig__ext1__Type := SCellConfig__ext1O__Type.
Definition SCellConfig__ext1__cond := SCellConfig__ext1O__cond.

Definition SCellConfig__ext2O__preConfGapStatus_r17__Type := bit_string_fixed.
Definition SCellConfig__ext2O__preConfGapStatus_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat maxNrofGapId_r17 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.GoodServingCellEvaluation_r17.

Opaque GoodServingCellEvaluation_r17__cond GoodServingCellEvaluation_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SCellSIB20_r17.
Definition SCellConfig__ext2O__sCellSIB20_r17__Type := SetupRelease__Type SCellSIB20_r17__Type.
Definition SCellConfig__ext2O__sCellSIB20_r17__cond := SetupRelease__cond _ SCellSIB20_r17__cond.
Definition SCellConfig__ext2O__sCellSIB20_r17__Format : T_Format SCellConfig__ext2O__sCellSIB20_r17__Type SCellConfig__ext2O__sCellSIB20_r17__cond := SetupRelease__Format _ _ SCellSIB20_r17__Format.
Opaque SCellConfig__ext2O__sCellSIB20_r17__cond SCellConfig__ext2O__sCellSIB20_r17__Format.

Record SCellConfig__ext2O__Type : Set :=
  make__SCellConfig__ext2O__Type {
    SCellConfig__ext2O__preConfGapStatus_r17 : option SCellConfig__ext2O__preConfGapStatus_r17__Type ;
    SCellConfig__ext2O__goodServingCellEvaluationBFD_r17 : option GoodServingCellEvaluation_r17__Type ;
    SCellConfig__ext2O__sCellSIB20_r17 : option SCellConfig__ext2O__sCellSIB20_r17__Type ;
}.
Definition SCellConfig__ext2O__list := (
 Opt SCellConfig__ext2O__preConfGapStatus_r17__Type SCellConfig__ext2O__preConfGapStatus_r17__cond ::
 Opt GoodServingCellEvaluation_r17__Type GoodServingCellEvaluation_r17__cond ::
 Opt SCellConfig__ext2O__sCellSIB20_r17__Type SCellConfig__ext2O__sCellSIB20_r17__cond ::
 nil).
Definition SCellConfig__ext2O__cond z := 
  opt_cond SCellConfig__ext2O__preConfGapStatus_r17__cond (SCellConfig__ext2O__preConfGapStatus_r17 z) /\
  opt_cond GoodServingCellEvaluation_r17__cond (SCellConfig__ext2O__goodServingCellEvaluationBFD_r17 z) /\
  opt_cond SCellConfig__ext2O__sCellSIB20_r17__cond (SCellConfig__ext2O__sCellSIB20_r17 z) /\
  True.

Definition SCellConfig__ext2__Type := SCellConfig__ext2O__Type.
Definition SCellConfig__ext2__cond := SCellConfig__ext2O__cond.

Record SCellConfig__Type : Set :=
  make__SCellConfig__Type {
    SCellConfig__sCellIndex : SCellIndex__Type ;
    SCellConfig__sCellConfigCommon : option ServingCellConfigCommon__Type ;
    SCellConfig__sCellConfigDedicated : option ServingCellConfig__Type ;
    SCellConfig__ext0 : option SCellConfig__ext0__Type ;
    SCellConfig__ext1 : option SCellConfig__ext1__Type ;
    SCellConfig__ext2 : option SCellConfig__ext2__Type ;
}.
Definition SCellConfig__root_list : list seq_elem := (
 Nor SCellIndex__Type SCellIndex__cond ::
 Opt ServingCellConfigCommon__Type ServingCellConfigCommon__cond ::
 Opt ServingCellConfig__Type ServingCellConfig__cond ::
 nil).
Definition SCellConfig__ext_list : list typ := (
  typ_cons SCellConfig__ext0__Type SCellConfig__ext0__cond ::
  typ_cons SCellConfig__ext1__Type SCellConfig__ext1__cond ::
  typ_cons SCellConfig__ext2__Type SCellConfig__ext2__cond ::
  nil).
Definition SCellConfig__cond (z : SCellConfig__Type) := 
(  SCellIndex__cond (SCellConfig__sCellIndex z) /\
  opt_cond ServingCellConfigCommon__cond (SCellConfig__sCellConfigCommon z) /\
  opt_cond ServingCellConfig__cond (SCellConfig__sCellConfigDedicated z) /\
  True) /\ 
(  opt_cond SCellConfig__ext0__cond (SCellConfig__ext0 z) /\
  opt_cond SCellConfig__ext1__cond (SCellConfig__ext1 z) /\
  opt_cond SCellConfig__ext2__cond (SCellConfig__ext2 z) /\
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

Definition SCellConfig__ext0O__Format_Type := Eval cbn in seq_format_prod SCellConfig__ext0O__list.
Definition SCellConfig__ext0O__Format_list : SCellConfig__ext0O__Format_Type :=
  (SSB_MTC__Format, unit_format).
Definition SCellConfig__ext0O__list__Format := (*Eval compute in *) seq_format SCellConfig__ext0O__list SCellConfig__ext0O__Format_list.
Definition SCellConfig__ext0O__F1 z :=
  (SCellConfig__ext0O__smtc z, tt).
Definition SCellConfig__ext0O__F2 (y : seq_type SCellConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SCellConfig__ext0O__Type i0
  end.
Lemma SCellConfig__ext0O__F1F2_cond (z : SCellConfig__ext0O__Type)
  : SCellConfig__ext0O__cond z ->
  (seq_cond SCellConfig__ext0O__list (SCellConfig__ext0O__F1 z)).
intro H. unfold SCellConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma SCellConfig__ext0O__F1F2_cond2 (z : SCellConfig__ext0O__Type)
 : SCellConfig__ext0O__F2 (SCellConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SCellConfig__ext0O__F2F1_cond (y : seq_type SCellConfig__ext0O__list)
  : seq_cond SCellConfig__ext0O__list y ->
 (SCellConfig__ext0O__cond (SCellConfig__ext0O__F2 y)) /\  SCellConfig__ext0O__F1 (SCellConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SCellConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold SCellConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SCellConfig__ext0O__Format : T_Format SCellConfig__ext0O__Type SCellConfig__ext0O__cond :=
        proj2_format  SCellConfig__ext0O__cond SCellConfig__ext0O__list__Format
    SCellConfig__ext0O__F1 SCellConfig__ext0O__F2 SCellConfig__ext0O__F1F2_cond  SCellConfig__ext0O__F1F2_cond2 SCellConfig__ext0O__F2F1_cond.
Opaque SCellConfig__ext0O__cond SCellConfig__ext0O__Format.

Definition SCellConfig__ext0__check_all_none (b : SCellConfig__ext0O__Type) : bool :=
match b with 
  | make__SCellConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SCellConfig__ext0__Format : T_Format SCellConfig__ext0__Type SCellConfig__ext0__cond :=
  restrict_add_format SCellConfig__ext0__check_all_none SCellConfig__ext0O__Format.

Opaque SCellConfig__ext0__cond SCellConfig__ext0__Format.

Definition SCellConfig__ext1O__sCellState_r16__Format : T_Format SCellConfig__ext1O__sCellState_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SCellConfig__ext1O__sCellState_r16__nat__Format SCellConfig__ext1O__sCellState_r16__F1 SCellConfig__ext1O__sCellState_r16__F2 SCellConfig__ext1O__sCellState_r16__F1F2 SCellConfig__ext1O__sCellState_r16__F2F1.

Opaque SCellConfig__ext1O__sCellState_r16__cond SCellConfig__ext1O__sCellState_r16__Format.

Definition SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Format : T_Format SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__nat__Format SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F1 SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F2 SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F1F2 SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__F2F1.

Opaque SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__cond SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Format.


Definition SCellConfig__ext1O__Format_Type := Eval cbn in seq_format_prod SCellConfig__ext1O__list.
Definition SCellConfig__ext1O__Format_list : SCellConfig__ext1O__Format_Type :=
  (SCellConfig__ext1O__sCellState_r16__Format, (SCellConfig__ext1O__secondaryDRX_GroupConfig_r16__Format, unit_format)).
Definition SCellConfig__ext1O__list__Format := (*Eval compute in *) seq_format SCellConfig__ext1O__list SCellConfig__ext1O__Format_list.
Definition SCellConfig__ext1O__F1 z :=
  (SCellConfig__ext1O__sCellState_r16 z, (SCellConfig__ext1O__secondaryDRX_GroupConfig_r16 z, tt)).
Definition SCellConfig__ext1O__F2 (y : seq_type SCellConfig__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SCellConfig__ext1O__Type i0 i1
  end.
Lemma SCellConfig__ext1O__F1F2_cond (z : SCellConfig__ext1O__Type)
  : SCellConfig__ext1O__cond z ->
  (seq_cond SCellConfig__ext1O__list (SCellConfig__ext1O__F1 z)).
intro H. unfold SCellConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma SCellConfig__ext1O__F1F2_cond2 (z : SCellConfig__ext1O__Type)
 : SCellConfig__ext1O__F2 (SCellConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SCellConfig__ext1O__F2F1_cond (y : seq_type SCellConfig__ext1O__list)
  : seq_cond SCellConfig__ext1O__list y ->
 (SCellConfig__ext1O__cond (SCellConfig__ext1O__F2 y)) /\  SCellConfig__ext1O__F1 (SCellConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SCellConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold SCellConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SCellConfig__ext1O__Format : T_Format SCellConfig__ext1O__Type SCellConfig__ext1O__cond :=
        proj2_format  SCellConfig__ext1O__cond SCellConfig__ext1O__list__Format
    SCellConfig__ext1O__F1 SCellConfig__ext1O__F2 SCellConfig__ext1O__F1F2_cond  SCellConfig__ext1O__F1F2_cond2 SCellConfig__ext1O__F2F1_cond.
Opaque SCellConfig__ext1O__cond SCellConfig__ext1O__Format.

Definition SCellConfig__ext1__check_all_none (b : SCellConfig__ext1O__Type) : bool :=
match b with 
  | make__SCellConfig__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition SCellConfig__ext1__Format : T_Format SCellConfig__ext1__Type SCellConfig__ext1__cond :=
  restrict_add_format SCellConfig__ext1__check_all_none SCellConfig__ext1O__Format.

Opaque SCellConfig__ext1__cond SCellConfig__ext1__Format.

Definition SCellConfig__ext2O__preConfGapStatus_r17__Format : T_Format SCellConfig__ext2O__preConfGapStatus_r17__Type SCellConfig__ext2O__preConfGapStatus_r17__cond := (* Eval compute in *) bit_string_fixed_format maxNrofGapId_r17.
Opaque SCellConfig__ext2O__preConfGapStatus_r17__cond SCellConfig__ext2O__preConfGapStatus_r17__Format.

Opaque SCellConfig__ext2O__sCellSIB20_r17__cond SCellConfig__ext2O__sCellSIB20_r17__Format.


Definition SCellConfig__ext2O__Format_Type := Eval cbn in seq_format_prod SCellConfig__ext2O__list.
Definition SCellConfig__ext2O__Format_list : SCellConfig__ext2O__Format_Type :=
  (SCellConfig__ext2O__preConfGapStatus_r17__Format, (GoodServingCellEvaluation_r17__Format, (SCellConfig__ext2O__sCellSIB20_r17__Format, unit_format))).
Definition SCellConfig__ext2O__list__Format := (*Eval compute in *) seq_format SCellConfig__ext2O__list SCellConfig__ext2O__Format_list.
Definition SCellConfig__ext2O__F1 z :=
  (SCellConfig__ext2O__preConfGapStatus_r17 z, (SCellConfig__ext2O__goodServingCellEvaluationBFD_r17 z, (SCellConfig__ext2O__sCellSIB20_r17 z, tt))).
Definition SCellConfig__ext2O__F2 (y : seq_type SCellConfig__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SCellConfig__ext2O__Type i0 i1 i2
  end.
Lemma SCellConfig__ext2O__F1F2_cond (z : SCellConfig__ext2O__Type)
  : SCellConfig__ext2O__cond z ->
  (seq_cond SCellConfig__ext2O__list (SCellConfig__ext2O__F1 z)).
intro H. unfold SCellConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma SCellConfig__ext2O__F1F2_cond2 (z : SCellConfig__ext2O__Type)
 : SCellConfig__ext2O__F2 (SCellConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SCellConfig__ext2O__F2F1_cond (y : seq_type SCellConfig__ext2O__list)
  : seq_cond SCellConfig__ext2O__list y ->
 (SCellConfig__ext2O__cond (SCellConfig__ext2O__F2 y)) /\  SCellConfig__ext2O__F1 (SCellConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SCellConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold SCellConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SCellConfig__ext2O__Format : T_Format SCellConfig__ext2O__Type SCellConfig__ext2O__cond :=
        proj2_format  SCellConfig__ext2O__cond SCellConfig__ext2O__list__Format
    SCellConfig__ext2O__F1 SCellConfig__ext2O__F2 SCellConfig__ext2O__F1F2_cond  SCellConfig__ext2O__F1F2_cond2 SCellConfig__ext2O__F2F1_cond.
Opaque SCellConfig__ext2O__cond SCellConfig__ext2O__Format.

Definition SCellConfig__ext2__check_all_none (b : SCellConfig__ext2O__Type) : bool :=
match b with 
  | make__SCellConfig__ext2O__Type None None None  => false 
  | _ => true 
 end.
Definition SCellConfig__ext2__Format : T_Format SCellConfig__ext2__Type SCellConfig__ext2__cond :=
  restrict_add_format SCellConfig__ext2__check_all_none SCellConfig__ext2O__Format.

Opaque SCellConfig__ext2__cond SCellConfig__ext2__Format.


Definition SCellConfig__root_Format_Type := Eval cbn in seq_format_prod SCellConfig__root_list.
Definition SCellConfig__root_Format_list : SCellConfig__root_Format_Type :=
  (SCellIndex__Format, (ServingCellConfigCommon__Format, (ServingCellConfig__Format, unit_format))).

Definition SCellConfig__ext_Format_Type := Eval cbn in get_formats SCellConfig__ext_list.
Definition SCellConfig__ext_Format_list : SCellConfig__ext_Format_Type :=
  (SCellConfig__ext0__Format, (SCellConfig__ext1__Format, (SCellConfig__ext2__Format, unit__Format))).

Definition SCellConfig__list_type : Set := (seq_type SCellConfig__root_list) * (seq_ext_type SCellConfig__ext_list).
Definition SCellConfig__list_cond (z : SCellConfig__list_type) : Prop :=
        (seq_cond SCellConfig__root_list (fst z)) /\ (seq_ext_cond SCellConfig__ext_list (snd z)).
Definition SCellConfig__list_format : T_Format SCellConfig__list_type SCellConfig__list_cond :=
 (* Eval compute in *) seq_ext_format SCellConfig__root_list SCellConfig__root_Format_list SCellConfig__ext_list SCellConfig__ext_Format_list.

Opaque SCellConfig__list_format.
Definition SCellConfig__F1 (z : SCellConfig__Type) : SCellConfig__list_type :=
  (((SCellConfig__sCellIndex z, (SCellConfig__sCellConfigCommon z, (SCellConfig__sCellConfigDedicated z, tt)))), (
(SCellConfig__ext0 z, (SCellConfig__ext1 z, (SCellConfig__ext2 z, tt))))).
Definition SCellConfig__F2 (y : SCellConfig__list_type) : SCellConfig__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, _))))=>
    make__SCellConfig__Type j0 j1 j2 i0 i1 i2
  end.
Definition SCellConfig__helper1 : (forall a : SCellConfig__Type, SCellConfig__cond a -> SCellConfig__list_cond (SCellConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SCellConfig__helper2 : (forall a : SCellConfig__Type, SCellConfig__F2 (SCellConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SCellConfig__helper3 : (forall b : SCellConfig__list_type, SCellConfig__list_cond b -> SCellConfig__cond (SCellConfig__F2 b) /\ SCellConfig__F1 (SCellConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SCellConfig__cond, SCellConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SCellConfig__Format : T_Format SCellConfig__Type SCellConfig__cond :=
 proj2_format SCellConfig__cond SCellConfig__list_format  SCellConfig__F1 SCellConfig__F2 SCellConfig__helper1 SCellConfig__helper2 SCellConfig__helper3.

Opaque SCellConfig__cond SCellConfig__Format.

