Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServingCellConfigCommon.

Opaque ServingCellConfigCommon__cond ServingCellConfigCommon__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Inductive ReconfigurationWithSync__t304__Type : Set :=
 | ReconfigurationWithSync__t304__ms50
 | ReconfigurationWithSync__t304__ms100
 | ReconfigurationWithSync__t304__ms150
 | ReconfigurationWithSync__t304__ms200
 | ReconfigurationWithSync__t304__ms500
 | ReconfigurationWithSync__t304__ms1000
 | ReconfigurationWithSync__t304__ms2000
 | ReconfigurationWithSync__t304__ms10000
.
Definition ReconfigurationWithSync__t304__cond := (fun (_ : ReconfigurationWithSync__t304__Type) => True).
Lemma ReconfigurationWithSync__t304__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReconfigurationWithSync__t304__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 ReconfigurationWithSync__t304__nat__helper.

Definition ReconfigurationWithSync__t304__F1 t :=
  match t with
  | ReconfigurationWithSync__t304__ms50 => 0
  | ReconfigurationWithSync__t304__ms100 => 1
  | ReconfigurationWithSync__t304__ms150 => 2
  | ReconfigurationWithSync__t304__ms200 => 3
  | ReconfigurationWithSync__t304__ms500 => 4
  | ReconfigurationWithSync__t304__ms1000 => 5
  | ReconfigurationWithSync__t304__ms2000 => 6
  | ReconfigurationWithSync__t304__ms10000 => 7
  end.
Definition ReconfigurationWithSync__t304__F2 n :=
  match n with
  | 0 => ReconfigurationWithSync__t304__ms50
  | 1 => ReconfigurationWithSync__t304__ms100
  | 2 => ReconfigurationWithSync__t304__ms150
  | 3 => ReconfigurationWithSync__t304__ms200
  | 4 => ReconfigurationWithSync__t304__ms500
  | 5 => ReconfigurationWithSync__t304__ms1000
  | 6 => ReconfigurationWithSync__t304__ms2000
  | 7 => ReconfigurationWithSync__t304__ms10000
  | _ => ReconfigurationWithSync__t304__ms50
  end.
Lemma ReconfigurationWithSync__t304__F1F2 : forall x : ReconfigurationWithSync__t304__Type, (ReconfigurationWithSync__t304__F1 x <= 7) /\ ReconfigurationWithSync__t304__F2 (ReconfigurationWithSync__t304__F1 x) = x. imp_solve. Qed.
Lemma ReconfigurationWithSync__t304__F2F1 : forall (y : nat) (H : y <= 7), ReconfigurationWithSync__t304__F1 (ReconfigurationWithSync__t304__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RACH_ConfigDedicated.

Opaque RACH_ConfigDedicated__cond RACH_ConfigDedicated__Format.

Require Import NR.RACH_ConfigDedicated.

Opaque RACH_ConfigDedicated__cond RACH_ConfigDedicated__Format.


Inductive ReconfigurationWithSync__rach_ConfigDedicated__Type : Set :=
  | ReconfigurationWithSync__rach_ConfigDedicated__uplink : RACH_ConfigDedicated__Type -> ReconfigurationWithSync__rach_ConfigDedicated__Type
  | ReconfigurationWithSync__rach_ConfigDedicated__supplementaryUplink : RACH_ConfigDedicated__Type -> ReconfigurationWithSync__rach_ConfigDedicated__Type
.
Definition ReconfigurationWithSync__rach_ConfigDedicated__list : list typ := (
typ_cons RACH_ConfigDedicated__Type RACH_ConfigDedicated__cond ::
typ_cons RACH_ConfigDedicated__Type RACH_ConfigDedicated__cond ::
 nil).
Definition ReconfigurationWithSync__rach_ConfigDedicated__cond (c : ReconfigurationWithSync__rach_ConfigDedicated__Type) := 
  match c with
  | ReconfigurationWithSync__rach_ConfigDedicated__uplink t => RACH_ConfigDedicated__cond t 
  | ReconfigurationWithSync__rach_ConfigDedicated__supplementaryUplink t => RACH_ConfigDedicated__cond t 
  end.

Lemma ReconfigurationWithSync__rach_ConfigDedicated__len_helper1 : to_bit_sz (length ReconfigurationWithSync__rach_ConfigDedicated__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ReconfigurationWithSync__rach_ConfigDedicated__len_helper2 : 2 <= length2 ReconfigurationWithSync__rach_ConfigDedicated__list.
 simpl. lia. Qed.
Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Record ReconfigurationWithSync__ext0O__Type : Set :=
  make__ReconfigurationWithSync__ext0O__Type {
    ReconfigurationWithSync__ext0O__smtc : option SSB_MTC__Type ;
}.
Definition ReconfigurationWithSync__ext0O__list := (
 Opt SSB_MTC__Type SSB_MTC__cond ::
 nil).
Definition ReconfigurationWithSync__ext0O__cond z := 
  opt_cond SSB_MTC__cond (ReconfigurationWithSync__ext0O__smtc z) /\
  True.

Definition ReconfigurationWithSync__ext0__Type := ReconfigurationWithSync__ext0O__Type.
Definition ReconfigurationWithSync__ext0__cond := ReconfigurationWithSync__ext0O__cond.

Require Import NR.DAPS_UplinkPowerConfig_r16.

Opaque DAPS_UplinkPowerConfig_r16__cond DAPS_UplinkPowerConfig_r16__Format.

Record ReconfigurationWithSync__ext1O__Type : Set :=
  make__ReconfigurationWithSync__ext1O__Type {
    ReconfigurationWithSync__ext1O__daps_UplinkPowerConfig_r16 : option DAPS_UplinkPowerConfig_r16__Type ;
}.
Definition ReconfigurationWithSync__ext1O__list := (
 Opt DAPS_UplinkPowerConfig_r16__Type DAPS_UplinkPowerConfig_r16__cond ::
 nil).
Definition ReconfigurationWithSync__ext1O__cond z := 
  opt_cond DAPS_UplinkPowerConfig_r16__cond (ReconfigurationWithSync__ext1O__daps_UplinkPowerConfig_r16 z) /\
  True.

Definition ReconfigurationWithSync__ext1__Type := ReconfigurationWithSync__ext1O__Type.
Definition ReconfigurationWithSync__ext1__cond := ReconfigurationWithSync__ext1O__cond.

Require Import NR.SL_PathSwitchConfig_r17.

Opaque SL_PathSwitchConfig_r17__cond SL_PathSwitchConfig_r17__Format.

Record ReconfigurationWithSync__ext2O__Type : Set :=
  make__ReconfigurationWithSync__ext2O__Type {
    ReconfigurationWithSync__ext2O__sl_PathSwitchConfig_r17 : option SL_PathSwitchConfig_r17__Type ;
}.
Definition ReconfigurationWithSync__ext2O__list := (
 Opt SL_PathSwitchConfig_r17__Type SL_PathSwitchConfig_r17__cond ::
 nil).
Definition ReconfigurationWithSync__ext2O__cond z := 
  opt_cond SL_PathSwitchConfig_r17__cond (ReconfigurationWithSync__ext2O__sl_PathSwitchConfig_r17 z) /\
  True.

Definition ReconfigurationWithSync__ext2__Type := ReconfigurationWithSync__ext2O__Type.
Definition ReconfigurationWithSync__ext2__cond := ReconfigurationWithSync__ext2O__cond.

Record ReconfigurationWithSync__Type : Set :=
  make__ReconfigurationWithSync__Type {
    ReconfigurationWithSync__spCellConfigCommon : option ServingCellConfigCommon__Type ;
    ReconfigurationWithSync__newUE_Identity : RNTI_Value__Type ;
    ReconfigurationWithSync__t304 : ReconfigurationWithSync__t304__Type ;
    ReconfigurationWithSync__rach_ConfigDedicated : option ReconfigurationWithSync__rach_ConfigDedicated__Type ;
    ReconfigurationWithSync__ext0 : option ReconfigurationWithSync__ext0__Type ;
    ReconfigurationWithSync__ext1 : option ReconfigurationWithSync__ext1__Type ;
    ReconfigurationWithSync__ext2 : option ReconfigurationWithSync__ext2__Type ;
}.
Definition ReconfigurationWithSync__root_list : list seq_elem := (
 Opt ServingCellConfigCommon__Type ServingCellConfigCommon__cond ::
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Nor ReconfigurationWithSync__t304__Type ReconfigurationWithSync__t304__cond ::
 Opt ReconfigurationWithSync__rach_ConfigDedicated__Type ReconfigurationWithSync__rach_ConfigDedicated__cond ::
 nil).
Definition ReconfigurationWithSync__ext_list : list typ := (
  typ_cons ReconfigurationWithSync__ext0__Type ReconfigurationWithSync__ext0__cond ::
  typ_cons ReconfigurationWithSync__ext1__Type ReconfigurationWithSync__ext1__cond ::
  typ_cons ReconfigurationWithSync__ext2__Type ReconfigurationWithSync__ext2__cond ::
  nil).
Definition ReconfigurationWithSync__cond (z : ReconfigurationWithSync__Type) := 
(  opt_cond ServingCellConfigCommon__cond (ReconfigurationWithSync__spCellConfigCommon z) /\
  RNTI_Value__cond (ReconfigurationWithSync__newUE_Identity z) /\
  ReconfigurationWithSync__t304__cond (ReconfigurationWithSync__t304 z) /\
  opt_cond ReconfigurationWithSync__rach_ConfigDedicated__cond (ReconfigurationWithSync__rach_ConfigDedicated z) /\
  True) /\ 
(  opt_cond ReconfigurationWithSync__ext0__cond (ReconfigurationWithSync__ext0 z) /\
  opt_cond ReconfigurationWithSync__ext1__cond (ReconfigurationWithSync__ext1 z) /\
  opt_cond ReconfigurationWithSync__ext2__cond (ReconfigurationWithSync__ext2 z) /\
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
Definition ReconfigurationWithSync__t304__Format : T_Format ReconfigurationWithSync__t304__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReconfigurationWithSync__t304__nat__Format ReconfigurationWithSync__t304__F1 ReconfigurationWithSync__t304__F2 ReconfigurationWithSync__t304__F1F2 ReconfigurationWithSync__t304__F2F1.

Opaque ReconfigurationWithSync__t304__cond ReconfigurationWithSync__t304__Format.


Definition ReconfigurationWithSync__rach_ConfigDedicated__Format_Type := Eval cbn in get_formats ReconfigurationWithSync__rach_ConfigDedicated__list.
Definition ReconfigurationWithSync__rach_ConfigDedicated__Format_list : ReconfigurationWithSync__rach_ConfigDedicated__Format_Type :=
  (RACH_ConfigDedicated__Format, (RACH_ConfigDedicated__Format, unit__Format)).
Definition ReconfigurationWithSync__rach_ConfigDedicated__list__Format := Eval compute in choice_format ReconfigurationWithSync__rach_ConfigDedicated__list ReconfigurationWithSync__rach_ConfigDedicated__len_helper1 ReconfigurationWithSync__rach_ConfigDedicated__len_helper2  ReconfigurationWithSync__rach_ConfigDedicated__Format_list.
Definition ReconfigurationWithSync__rach_ConfigDedicated__F1 (z : ReconfigurationWithSync__rach_ConfigDedicated__Type) : (choice ReconfigurationWithSync__rach_ConfigDedicated__list) :=
  match z with
   | ReconfigurationWithSync__rach_ConfigDedicated__uplink t => existT _ 0 t
  | ReconfigurationWithSync__rach_ConfigDedicated__supplementaryUplink t => existT _ 1 t
  end.
Definition ReconfigurationWithSync__rach_ConfigDedicated__g := (fun n => typ_set (get_nth_typ ReconfigurationWithSync__rach_ConfigDedicated__list n)).
Definition ReconfigurationWithSync__rach_ConfigDedicated__F2 (y : choice ReconfigurationWithSync__rach_ConfigDedicated__list) : ReconfigurationWithSync__rach_ConfigDedicated__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ReconfigurationWithSync__rach_ConfigDedicated__g n -> ReconfigurationWithSync__rach_ConfigDedicated__Type) with
    | 0 => fun (t : RACH_ConfigDedicated__Type) => ReconfigurationWithSync__rach_ConfigDedicated__uplink t 
    | 1 => fun (t : RACH_ConfigDedicated__Type) => ReconfigurationWithSync__rach_ConfigDedicated__supplementaryUplink t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ReconfigurationWithSync__rach_ConfigDedicated__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ReconfigurationWithSync__rach_ConfigDedicated__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ReconfigurationWithSync__rach_ConfigDedicated__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ReconfigurationWithSync__rach_ConfigDedicated__Type with end) n0
           end t0).

Lemma ReconfigurationWithSync__rach_ConfigDedicated__helper2 :  forall (y : ReconfigurationWithSync__rach_ConfigDedicated__Type), ReconfigurationWithSync__rach_ConfigDedicated__cond y -> choice_cond ReconfigurationWithSync__rach_ConfigDedicated__list (ReconfigurationWithSync__rach_ConfigDedicated__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ReconfigurationWithSync__rach_ConfigDedicated__helper3 :  forall (y : ReconfigurationWithSync__rach_ConfigDedicated__Type), ReconfigurationWithSync__rach_ConfigDedicated__F2 (ReconfigurationWithSync__rach_ConfigDedicated__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ReconfigurationWithSync__rach_ConfigDedicated__helper4 : (forall b : choice ReconfigurationWithSync__rach_ConfigDedicated__list, choice_cond ReconfigurationWithSync__rach_ConfigDedicated__list b -> ReconfigurationWithSync__rach_ConfigDedicated__cond (ReconfigurationWithSync__rach_ConfigDedicated__F2 b) /\ ReconfigurationWithSync__rach_ConfigDedicated__F1 (ReconfigurationWithSync__rach_ConfigDedicated__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ReconfigurationWithSync__rach_ConfigDedicated__F1 ReconfigurationWithSync__rach_ConfigDedicated__F2.
Definition ReconfigurationWithSync__rach_ConfigDedicated__Format : T_Format ReconfigurationWithSync__rach_ConfigDedicated__Type ReconfigurationWithSync__rach_ConfigDedicated__cond :=
  (* Eval compute in *) proj2_format ReconfigurationWithSync__rach_ConfigDedicated__cond ReconfigurationWithSync__rach_ConfigDedicated__list__Format ReconfigurationWithSync__rach_ConfigDedicated__F1 ReconfigurationWithSync__rach_ConfigDedicated__F2 ReconfigurationWithSync__rach_ConfigDedicated__helper2 ReconfigurationWithSync__rach_ConfigDedicated__helper3 ReconfigurationWithSync__rach_ConfigDedicated__helper4.
Opaque ReconfigurationWithSync__rach_ConfigDedicated__cond ReconfigurationWithSync__rach_ConfigDedicated__Format.


Definition ReconfigurationWithSync__ext0O__Format_Type := Eval cbn in seq_format_prod ReconfigurationWithSync__ext0O__list.
Definition ReconfigurationWithSync__ext0O__Format_list : ReconfigurationWithSync__ext0O__Format_Type :=
  (SSB_MTC__Format, unit_format).
Definition ReconfigurationWithSync__ext0O__list__Format := (*Eval compute in *) seq_format ReconfigurationWithSync__ext0O__list ReconfigurationWithSync__ext0O__Format_list.
Definition ReconfigurationWithSync__ext0O__F1 z :=
  (ReconfigurationWithSync__ext0O__smtc z, tt).
Definition ReconfigurationWithSync__ext0O__F2 (y : seq_type ReconfigurationWithSync__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__ReconfigurationWithSync__ext0O__Type i0
  end.
Lemma ReconfigurationWithSync__ext0O__F1F2_cond (z : ReconfigurationWithSync__ext0O__Type)
  : ReconfigurationWithSync__ext0O__cond z ->
  (seq_cond ReconfigurationWithSync__ext0O__list (ReconfigurationWithSync__ext0O__F1 z)).
intro H. unfold ReconfigurationWithSync__ext0O__cond in H. simpl. auto. Qed.
Lemma ReconfigurationWithSync__ext0O__F1F2_cond2 (z : ReconfigurationWithSync__ext0O__Type)
 : ReconfigurationWithSync__ext0O__F2 (ReconfigurationWithSync__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReconfigurationWithSync__ext0O__F2F1_cond (y : seq_type ReconfigurationWithSync__ext0O__list)
  : seq_cond ReconfigurationWithSync__ext0O__list y ->
 (ReconfigurationWithSync__ext0O__cond (ReconfigurationWithSync__ext0O__F2 y)) /\  ReconfigurationWithSync__ext0O__F1 (ReconfigurationWithSync__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReconfigurationWithSync__ext0O__cond. simpl in *. auto.
 - simpl. unfold ReconfigurationWithSync__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReconfigurationWithSync__ext0O__Format : T_Format ReconfigurationWithSync__ext0O__Type ReconfigurationWithSync__ext0O__cond :=
        proj2_format  ReconfigurationWithSync__ext0O__cond ReconfigurationWithSync__ext0O__list__Format
    ReconfigurationWithSync__ext0O__F1 ReconfigurationWithSync__ext0O__F2 ReconfigurationWithSync__ext0O__F1F2_cond  ReconfigurationWithSync__ext0O__F1F2_cond2 ReconfigurationWithSync__ext0O__F2F1_cond.
Opaque ReconfigurationWithSync__ext0O__cond ReconfigurationWithSync__ext0O__Format.

Definition ReconfigurationWithSync__ext0__check_all_none (b : ReconfigurationWithSync__ext0O__Type) : bool :=
match b with 
  | make__ReconfigurationWithSync__ext0O__Type None  => false 
  | _ => true 
 end.
Definition ReconfigurationWithSync__ext0__Format : T_Format ReconfigurationWithSync__ext0__Type ReconfigurationWithSync__ext0__cond :=
  restrict_add_format ReconfigurationWithSync__ext0__check_all_none ReconfigurationWithSync__ext0O__Format.

Opaque ReconfigurationWithSync__ext0__cond ReconfigurationWithSync__ext0__Format.


Definition ReconfigurationWithSync__ext1O__Format_Type := Eval cbn in seq_format_prod ReconfigurationWithSync__ext1O__list.
Definition ReconfigurationWithSync__ext1O__Format_list : ReconfigurationWithSync__ext1O__Format_Type :=
  (DAPS_UplinkPowerConfig_r16__Format, unit_format).
Definition ReconfigurationWithSync__ext1O__list__Format := (*Eval compute in *) seq_format ReconfigurationWithSync__ext1O__list ReconfigurationWithSync__ext1O__Format_list.
Definition ReconfigurationWithSync__ext1O__F1 z :=
  (ReconfigurationWithSync__ext1O__daps_UplinkPowerConfig_r16 z, tt).
Definition ReconfigurationWithSync__ext1O__F2 (y : seq_type ReconfigurationWithSync__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__ReconfigurationWithSync__ext1O__Type i0
  end.
Lemma ReconfigurationWithSync__ext1O__F1F2_cond (z : ReconfigurationWithSync__ext1O__Type)
  : ReconfigurationWithSync__ext1O__cond z ->
  (seq_cond ReconfigurationWithSync__ext1O__list (ReconfigurationWithSync__ext1O__F1 z)).
intro H. unfold ReconfigurationWithSync__ext1O__cond in H. simpl. auto. Qed.
Lemma ReconfigurationWithSync__ext1O__F1F2_cond2 (z : ReconfigurationWithSync__ext1O__Type)
 : ReconfigurationWithSync__ext1O__F2 (ReconfigurationWithSync__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReconfigurationWithSync__ext1O__F2F1_cond (y : seq_type ReconfigurationWithSync__ext1O__list)
  : seq_cond ReconfigurationWithSync__ext1O__list y ->
 (ReconfigurationWithSync__ext1O__cond (ReconfigurationWithSync__ext1O__F2 y)) /\  ReconfigurationWithSync__ext1O__F1 (ReconfigurationWithSync__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReconfigurationWithSync__ext1O__cond. simpl in *. auto.
 - simpl. unfold ReconfigurationWithSync__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReconfigurationWithSync__ext1O__Format : T_Format ReconfigurationWithSync__ext1O__Type ReconfigurationWithSync__ext1O__cond :=
        proj2_format  ReconfigurationWithSync__ext1O__cond ReconfigurationWithSync__ext1O__list__Format
    ReconfigurationWithSync__ext1O__F1 ReconfigurationWithSync__ext1O__F2 ReconfigurationWithSync__ext1O__F1F2_cond  ReconfigurationWithSync__ext1O__F1F2_cond2 ReconfigurationWithSync__ext1O__F2F1_cond.
Opaque ReconfigurationWithSync__ext1O__cond ReconfigurationWithSync__ext1O__Format.

Definition ReconfigurationWithSync__ext1__check_all_none (b : ReconfigurationWithSync__ext1O__Type) : bool :=
match b with 
  | make__ReconfigurationWithSync__ext1O__Type None  => false 
  | _ => true 
 end.
Definition ReconfigurationWithSync__ext1__Format : T_Format ReconfigurationWithSync__ext1__Type ReconfigurationWithSync__ext1__cond :=
  restrict_add_format ReconfigurationWithSync__ext1__check_all_none ReconfigurationWithSync__ext1O__Format.

Opaque ReconfigurationWithSync__ext1__cond ReconfigurationWithSync__ext1__Format.


Definition ReconfigurationWithSync__ext2O__Format_Type := Eval cbn in seq_format_prod ReconfigurationWithSync__ext2O__list.
Definition ReconfigurationWithSync__ext2O__Format_list : ReconfigurationWithSync__ext2O__Format_Type :=
  (SL_PathSwitchConfig_r17__Format, unit_format).
Definition ReconfigurationWithSync__ext2O__list__Format := (*Eval compute in *) seq_format ReconfigurationWithSync__ext2O__list ReconfigurationWithSync__ext2O__Format_list.
Definition ReconfigurationWithSync__ext2O__F1 z :=
  (ReconfigurationWithSync__ext2O__sl_PathSwitchConfig_r17 z, tt).
Definition ReconfigurationWithSync__ext2O__F2 (y : seq_type ReconfigurationWithSync__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__ReconfigurationWithSync__ext2O__Type i0
  end.
Lemma ReconfigurationWithSync__ext2O__F1F2_cond (z : ReconfigurationWithSync__ext2O__Type)
  : ReconfigurationWithSync__ext2O__cond z ->
  (seq_cond ReconfigurationWithSync__ext2O__list (ReconfigurationWithSync__ext2O__F1 z)).
intro H. unfold ReconfigurationWithSync__ext2O__cond in H. simpl. auto. Qed.
Lemma ReconfigurationWithSync__ext2O__F1F2_cond2 (z : ReconfigurationWithSync__ext2O__Type)
 : ReconfigurationWithSync__ext2O__F2 (ReconfigurationWithSync__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReconfigurationWithSync__ext2O__F2F1_cond (y : seq_type ReconfigurationWithSync__ext2O__list)
  : seq_cond ReconfigurationWithSync__ext2O__list y ->
 (ReconfigurationWithSync__ext2O__cond (ReconfigurationWithSync__ext2O__F2 y)) /\  ReconfigurationWithSync__ext2O__F1 (ReconfigurationWithSync__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReconfigurationWithSync__ext2O__cond. simpl in *. auto.
 - simpl. unfold ReconfigurationWithSync__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReconfigurationWithSync__ext2O__Format : T_Format ReconfigurationWithSync__ext2O__Type ReconfigurationWithSync__ext2O__cond :=
        proj2_format  ReconfigurationWithSync__ext2O__cond ReconfigurationWithSync__ext2O__list__Format
    ReconfigurationWithSync__ext2O__F1 ReconfigurationWithSync__ext2O__F2 ReconfigurationWithSync__ext2O__F1F2_cond  ReconfigurationWithSync__ext2O__F1F2_cond2 ReconfigurationWithSync__ext2O__F2F1_cond.
Opaque ReconfigurationWithSync__ext2O__cond ReconfigurationWithSync__ext2O__Format.

Definition ReconfigurationWithSync__ext2__check_all_none (b : ReconfigurationWithSync__ext2O__Type) : bool :=
match b with 
  | make__ReconfigurationWithSync__ext2O__Type None  => false 
  | _ => true 
 end.
Definition ReconfigurationWithSync__ext2__Format : T_Format ReconfigurationWithSync__ext2__Type ReconfigurationWithSync__ext2__cond :=
  restrict_add_format ReconfigurationWithSync__ext2__check_all_none ReconfigurationWithSync__ext2O__Format.

Opaque ReconfigurationWithSync__ext2__cond ReconfigurationWithSync__ext2__Format.


Definition ReconfigurationWithSync__root_Format_Type := Eval cbn in seq_format_prod ReconfigurationWithSync__root_list.
Definition ReconfigurationWithSync__root_Format_list : ReconfigurationWithSync__root_Format_Type :=
  (ServingCellConfigCommon__Format, (RNTI_Value__Format, (ReconfigurationWithSync__t304__Format, (ReconfigurationWithSync__rach_ConfigDedicated__Format, unit_format)))).

Definition ReconfigurationWithSync__ext_Format_Type := Eval cbn in get_formats ReconfigurationWithSync__ext_list.
Definition ReconfigurationWithSync__ext_Format_list : ReconfigurationWithSync__ext_Format_Type :=
  (ReconfigurationWithSync__ext0__Format, (ReconfigurationWithSync__ext1__Format, (ReconfigurationWithSync__ext2__Format, unit__Format))).

Definition ReconfigurationWithSync__list_type : Set := (seq_type ReconfigurationWithSync__root_list) * (seq_ext_type ReconfigurationWithSync__ext_list).
Definition ReconfigurationWithSync__list_cond (z : ReconfigurationWithSync__list_type) : Prop :=
        (seq_cond ReconfigurationWithSync__root_list (fst z)) /\ (seq_ext_cond ReconfigurationWithSync__ext_list (snd z)).
Definition ReconfigurationWithSync__list_format : T_Format ReconfigurationWithSync__list_type ReconfigurationWithSync__list_cond :=
 (* Eval compute in *) seq_ext_format ReconfigurationWithSync__root_list ReconfigurationWithSync__root_Format_list ReconfigurationWithSync__ext_list ReconfigurationWithSync__ext_Format_list.

Opaque ReconfigurationWithSync__list_format.
Definition ReconfigurationWithSync__F1 (z : ReconfigurationWithSync__Type) : ReconfigurationWithSync__list_type :=
  (((ReconfigurationWithSync__spCellConfigCommon z, (ReconfigurationWithSync__newUE_Identity z, (ReconfigurationWithSync__t304 z, (ReconfigurationWithSync__rach_ConfigDedicated z, tt))))), (
(ReconfigurationWithSync__ext0 z, (ReconfigurationWithSync__ext1 z, (ReconfigurationWithSync__ext2 z, tt))))).
Definition ReconfigurationWithSync__F2 (y : ReconfigurationWithSync__list_type) : ReconfigurationWithSync__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, (i2, _))))=>
    make__ReconfigurationWithSync__Type j0 j1 j2 j3 i0 i1 i2
  end.
Definition ReconfigurationWithSync__helper1 : (forall a : ReconfigurationWithSync__Type, ReconfigurationWithSync__cond a -> ReconfigurationWithSync__list_cond (ReconfigurationWithSync__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ReconfigurationWithSync__helper2 : (forall a : ReconfigurationWithSync__Type, ReconfigurationWithSync__F2 (ReconfigurationWithSync__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ReconfigurationWithSync__helper3 : (forall b : ReconfigurationWithSync__list_type, ReconfigurationWithSync__list_cond b -> ReconfigurationWithSync__cond (ReconfigurationWithSync__F2 b) /\ ReconfigurationWithSync__F1 (ReconfigurationWithSync__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ReconfigurationWithSync__cond, ReconfigurationWithSync__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ReconfigurationWithSync__Format : T_Format ReconfigurationWithSync__Type ReconfigurationWithSync__cond :=
 proj2_format ReconfigurationWithSync__cond ReconfigurationWithSync__list_format  ReconfigurationWithSync__F1 ReconfigurationWithSync__F2 ReconfigurationWithSync__helper1 ReconfigurationWithSync__helper2 ReconfigurationWithSync__helper3.

Opaque ReconfigurationWithSync__cond ReconfigurationWithSync__Format.

