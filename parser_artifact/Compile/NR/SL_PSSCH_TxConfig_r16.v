Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_TypeTxSync_r16.

Opaque SL_TypeTxSync_r16__cond SL_TypeTxSync_r16__Format.

Inductive SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Type : Set :=
 | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph60
 | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph80
 | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph100
 | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph120
 | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph140
 | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph160
 | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph180
 | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph200
.
Definition SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__cond := (fun (_ : SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Type) => True).
Lemma SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__nat__helper.

Definition SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F1 t :=
  match t with
  | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph60 => 0
  | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph80 => 1
  | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph100 => 2
  | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph120 => 3
  | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph140 => 4
  | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph160 => 5
  | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph180 => 6
  | SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph200 => 7
  end.
Definition SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F2 n :=
  match n with
  | 0 => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph60
  | 1 => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph80
  | 2 => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph100
  | 3 => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph120
  | 4 => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph140
  | 5 => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph160
  | 6 => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph180
  | 7 => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph200
  | _ => SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__kmph60
  end.
Lemma SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F1F2 : forall x : SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Type, (SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F1 x <= 7) /\ SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F2 (SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F1 (SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_PSSCH_TxParameters_r16.

Opaque SL_PSSCH_TxParameters_r16__cond SL_PSSCH_TxParameters_r16__Format.

Require Import NR.SL_PSSCH_TxParameters_r16.

Opaque SL_PSSCH_TxParameters_r16__cond SL_PSSCH_TxParameters_r16__Format.

Require Import NR.SL_MinMaxMCS_List_r16.

Opaque SL_MinMaxMCS_List_r16__cond SL_MinMaxMCS_List_r16__Format.

Require Import NR.SL_MinMaxMCS_List_r16.

Opaque SL_MinMaxMCS_List_r16__cond SL_MinMaxMCS_List_r16__Format.

Record SL_PSSCH_TxConfig_r16__ext0O__Type : Set :=
  make__SL_PSSCH_TxConfig_r16__ext0O__Type {
    SL_PSSCH_TxConfig_r16__ext0O__sl_ParametersAboveThres_v1650 : option SL_MinMaxMCS_List_r16__Type ;
    SL_PSSCH_TxConfig_r16__ext0O__sl_ParametersBelowThres_v1650 : option SL_MinMaxMCS_List_r16__Type ;
}.
Definition SL_PSSCH_TxConfig_r16__ext0O__list := (
 Opt SL_MinMaxMCS_List_r16__Type SL_MinMaxMCS_List_r16__cond ::
 Opt SL_MinMaxMCS_List_r16__Type SL_MinMaxMCS_List_r16__cond ::
 nil).
Definition SL_PSSCH_TxConfig_r16__ext0O__cond z := 
  opt_cond SL_MinMaxMCS_List_r16__cond (SL_PSSCH_TxConfig_r16__ext0O__sl_ParametersAboveThres_v1650 z) /\
  opt_cond SL_MinMaxMCS_List_r16__cond (SL_PSSCH_TxConfig_r16__ext0O__sl_ParametersBelowThres_v1650 z) /\
  True.

Definition SL_PSSCH_TxConfig_r16__ext0__Type := SL_PSSCH_TxConfig_r16__ext0O__Type.
Definition SL_PSSCH_TxConfig_r16__ext0__cond := SL_PSSCH_TxConfig_r16__ext0O__cond.

Record SL_PSSCH_TxConfig_r16__Type : Set :=
  make__SL_PSSCH_TxConfig_r16__Type {
    SL_PSSCH_TxConfig_r16__sl_TypeTxSync_r16 : option SL_TypeTxSync_r16__Type ;
    SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16 : SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Type ;
    SL_PSSCH_TxConfig_r16__sl_ParametersAboveThres_r16 : SL_PSSCH_TxParameters_r16__Type ;
    SL_PSSCH_TxConfig_r16__sl_ParametersBelowThres_r16 : SL_PSSCH_TxParameters_r16__Type ;
    SL_PSSCH_TxConfig_r16__ext0 : option SL_PSSCH_TxConfig_r16__ext0__Type ;
}.
Definition SL_PSSCH_TxConfig_r16__root_list : list seq_elem := (
 Opt SL_TypeTxSync_r16__Type SL_TypeTxSync_r16__cond ::
 Nor SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Type SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__cond ::
 Nor SL_PSSCH_TxParameters_r16__Type SL_PSSCH_TxParameters_r16__cond ::
 Nor SL_PSSCH_TxParameters_r16__Type SL_PSSCH_TxParameters_r16__cond ::
 nil).
Definition SL_PSSCH_TxConfig_r16__ext_list : list typ := (
  typ_cons SL_PSSCH_TxConfig_r16__ext0__Type SL_PSSCH_TxConfig_r16__ext0__cond ::
  nil).
Definition SL_PSSCH_TxConfig_r16__cond (z : SL_PSSCH_TxConfig_r16__Type) := 
(  opt_cond SL_TypeTxSync_r16__cond (SL_PSSCH_TxConfig_r16__sl_TypeTxSync_r16 z) /\
  SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__cond (SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16 z) /\
  SL_PSSCH_TxParameters_r16__cond (SL_PSSCH_TxConfig_r16__sl_ParametersAboveThres_r16 z) /\
  SL_PSSCH_TxParameters_r16__cond (SL_PSSCH_TxConfig_r16__sl_ParametersBelowThres_r16 z) /\
  True) /\ 
(  opt_cond SL_PSSCH_TxConfig_r16__ext0__cond (SL_PSSCH_TxConfig_r16__ext0 z) /\
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
Definition SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Format : T_Format SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__nat__Format SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F1 SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F2 SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F1F2 SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__F2F1.

Opaque SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__cond SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Format.


Definition SL_PSSCH_TxConfig_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SL_PSSCH_TxConfig_r16__ext0O__list.
Definition SL_PSSCH_TxConfig_r16__ext0O__Format_list : SL_PSSCH_TxConfig_r16__ext0O__Format_Type :=
  (SL_MinMaxMCS_List_r16__Format, (SL_MinMaxMCS_List_r16__Format, unit_format)).
Definition SL_PSSCH_TxConfig_r16__ext0O__list__Format := (*Eval compute in *) seq_format SL_PSSCH_TxConfig_r16__ext0O__list SL_PSSCH_TxConfig_r16__ext0O__Format_list.
Definition SL_PSSCH_TxConfig_r16__ext0O__F1 z :=
  (SL_PSSCH_TxConfig_r16__ext0O__sl_ParametersAboveThres_v1650 z, (SL_PSSCH_TxConfig_r16__ext0O__sl_ParametersBelowThres_v1650 z, tt)).
Definition SL_PSSCH_TxConfig_r16__ext0O__F2 (y : seq_type SL_PSSCH_TxConfig_r16__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SL_PSSCH_TxConfig_r16__ext0O__Type i0 i1
  end.
Lemma SL_PSSCH_TxConfig_r16__ext0O__F1F2_cond (z : SL_PSSCH_TxConfig_r16__ext0O__Type)
  : SL_PSSCH_TxConfig_r16__ext0O__cond z ->
  (seq_cond SL_PSSCH_TxConfig_r16__ext0O__list (SL_PSSCH_TxConfig_r16__ext0O__F1 z)).
intro H. unfold SL_PSSCH_TxConfig_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SL_PSSCH_TxConfig_r16__ext0O__F1F2_cond2 (z : SL_PSSCH_TxConfig_r16__ext0O__Type)
 : SL_PSSCH_TxConfig_r16__ext0O__F2 (SL_PSSCH_TxConfig_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_PSSCH_TxConfig_r16__ext0O__F2F1_cond (y : seq_type SL_PSSCH_TxConfig_r16__ext0O__list)
  : seq_cond SL_PSSCH_TxConfig_r16__ext0O__list y ->
 (SL_PSSCH_TxConfig_r16__ext0O__cond (SL_PSSCH_TxConfig_r16__ext0O__F2 y)) /\  SL_PSSCH_TxConfig_r16__ext0O__F1 (SL_PSSCH_TxConfig_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_PSSCH_TxConfig_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SL_PSSCH_TxConfig_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_PSSCH_TxConfig_r16__ext0O__Format : T_Format SL_PSSCH_TxConfig_r16__ext0O__Type SL_PSSCH_TxConfig_r16__ext0O__cond :=
        proj2_format  SL_PSSCH_TxConfig_r16__ext0O__cond SL_PSSCH_TxConfig_r16__ext0O__list__Format
    SL_PSSCH_TxConfig_r16__ext0O__F1 SL_PSSCH_TxConfig_r16__ext0O__F2 SL_PSSCH_TxConfig_r16__ext0O__F1F2_cond  SL_PSSCH_TxConfig_r16__ext0O__F1F2_cond2 SL_PSSCH_TxConfig_r16__ext0O__F2F1_cond.
Opaque SL_PSSCH_TxConfig_r16__ext0O__cond SL_PSSCH_TxConfig_r16__ext0O__Format.

Definition SL_PSSCH_TxConfig_r16__ext0__check_all_none (b : SL_PSSCH_TxConfig_r16__ext0O__Type) : bool :=
match b with 
  | make__SL_PSSCH_TxConfig_r16__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition SL_PSSCH_TxConfig_r16__ext0__Format : T_Format SL_PSSCH_TxConfig_r16__ext0__Type SL_PSSCH_TxConfig_r16__ext0__cond :=
  restrict_add_format SL_PSSCH_TxConfig_r16__ext0__check_all_none SL_PSSCH_TxConfig_r16__ext0O__Format.

Opaque SL_PSSCH_TxConfig_r16__ext0__cond SL_PSSCH_TxConfig_r16__ext0__Format.


Definition SL_PSSCH_TxConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_PSSCH_TxConfig_r16__root_list.
Definition SL_PSSCH_TxConfig_r16__root_Format_list : SL_PSSCH_TxConfig_r16__root_Format_Type :=
  (SL_TypeTxSync_r16__Format, (SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16__Format, (SL_PSSCH_TxParameters_r16__Format, (SL_PSSCH_TxParameters_r16__Format, unit_format)))).

Definition SL_PSSCH_TxConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_PSSCH_TxConfig_r16__ext_list.
Definition SL_PSSCH_TxConfig_r16__ext_Format_list : SL_PSSCH_TxConfig_r16__ext_Format_Type :=
  (SL_PSSCH_TxConfig_r16__ext0__Format, unit__Format).

Definition SL_PSSCH_TxConfig_r16__list_type : Set := (seq_type SL_PSSCH_TxConfig_r16__root_list) * (seq_ext_type SL_PSSCH_TxConfig_r16__ext_list).
Definition SL_PSSCH_TxConfig_r16__list_cond (z : SL_PSSCH_TxConfig_r16__list_type) : Prop :=
        (seq_cond SL_PSSCH_TxConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_PSSCH_TxConfig_r16__ext_list (snd z)).
Definition SL_PSSCH_TxConfig_r16__list_format : T_Format SL_PSSCH_TxConfig_r16__list_type SL_PSSCH_TxConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_PSSCH_TxConfig_r16__root_list SL_PSSCH_TxConfig_r16__root_Format_list SL_PSSCH_TxConfig_r16__ext_list SL_PSSCH_TxConfig_r16__ext_Format_list.

Opaque SL_PSSCH_TxConfig_r16__list_format.
Definition SL_PSSCH_TxConfig_r16__F1 (z : SL_PSSCH_TxConfig_r16__Type) : SL_PSSCH_TxConfig_r16__list_type :=
  (((SL_PSSCH_TxConfig_r16__sl_TypeTxSync_r16 z, (SL_PSSCH_TxConfig_r16__sl_ThresUE_Speed_r16 z, (SL_PSSCH_TxConfig_r16__sl_ParametersAboveThres_r16 z, (SL_PSSCH_TxConfig_r16__sl_ParametersBelowThres_r16 z, tt))))), (
(SL_PSSCH_TxConfig_r16__ext0 z, tt))).
Definition SL_PSSCH_TxConfig_r16__F2 (y : SL_PSSCH_TxConfig_r16__list_type) : SL_PSSCH_TxConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__SL_PSSCH_TxConfig_r16__Type j0 j1 j2 j3 i0
  end.
Definition SL_PSSCH_TxConfig_r16__helper1 : (forall a : SL_PSSCH_TxConfig_r16__Type, SL_PSSCH_TxConfig_r16__cond a -> SL_PSSCH_TxConfig_r16__list_cond (SL_PSSCH_TxConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_PSSCH_TxConfig_r16__helper2 : (forall a : SL_PSSCH_TxConfig_r16__Type, SL_PSSCH_TxConfig_r16__F2 (SL_PSSCH_TxConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_PSSCH_TxConfig_r16__helper3 : (forall b : SL_PSSCH_TxConfig_r16__list_type, SL_PSSCH_TxConfig_r16__list_cond b -> SL_PSSCH_TxConfig_r16__cond (SL_PSSCH_TxConfig_r16__F2 b) /\ SL_PSSCH_TxConfig_r16__F1 (SL_PSSCH_TxConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_PSSCH_TxConfig_r16__cond, SL_PSSCH_TxConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_PSSCH_TxConfig_r16__Format : T_Format SL_PSSCH_TxConfig_r16__Type SL_PSSCH_TxConfig_r16__cond :=
 proj2_format SL_PSSCH_TxConfig_r16__cond SL_PSSCH_TxConfig_r16__list_format  SL_PSSCH_TxConfig_r16__F1 SL_PSSCH_TxConfig_r16__F2 SL_PSSCH_TxConfig_r16__helper1 SL_PSSCH_TxConfig_r16__helper2 SL_PSSCH_TxConfig_r16__helper3.

Opaque SL_PSSCH_TxConfig_r16__cond SL_PSSCH_TxConfig_r16__Format.

