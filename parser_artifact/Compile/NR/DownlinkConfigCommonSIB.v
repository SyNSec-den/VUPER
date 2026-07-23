Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FrequencyInfoDL_SIB.

Opaque FrequencyInfoDL_SIB__cond FrequencyInfoDL_SIB__Format.

Require Import NR.BWP_DownlinkCommon.

Opaque BWP_DownlinkCommon__cond BWP_DownlinkCommon__Format.

Require Import NR.BCCH_Config.

Opaque BCCH_Config__cond BCCH_Config__Format.

Require Import NR.PCCH_Config.

Opaque PCCH_Config__cond PCCH_Config__Format.

Require Import NR.PEI_Config_r17.

Opaque PEI_Config_r17__cond PEI_Config_r17__Format.

Require Import NR.BWP_DownlinkCommon.

Opaque BWP_DownlinkCommon__cond BWP_DownlinkCommon__Format.

Record DownlinkConfigCommonSIB__ext0O__Type : Set :=
  make__DownlinkConfigCommonSIB__ext0O__Type {
    DownlinkConfigCommonSIB__ext0O__pei_Config_r17 : option PEI_Config_r17__Type ;
    DownlinkConfigCommonSIB__ext0O__initialDownlinkBWP_RedCap_r17 : option BWP_DownlinkCommon__Type ;
}.
Definition DownlinkConfigCommonSIB__ext0O__list := (
 Opt PEI_Config_r17__Type PEI_Config_r17__cond ::
 Opt BWP_DownlinkCommon__Type BWP_DownlinkCommon__cond ::
 nil).
Definition DownlinkConfigCommonSIB__ext0O__cond z := 
  opt_cond PEI_Config_r17__cond (DownlinkConfigCommonSIB__ext0O__pei_Config_r17 z) /\
  opt_cond BWP_DownlinkCommon__cond (DownlinkConfigCommonSIB__ext0O__initialDownlinkBWP_RedCap_r17 z) /\
  True.

Definition DownlinkConfigCommonSIB__ext0__Type := DownlinkConfigCommonSIB__ext0O__Type.
Definition DownlinkConfigCommonSIB__ext0__cond := DownlinkConfigCommonSIB__ext0O__cond.

Record DownlinkConfigCommonSIB__Type : Set :=
  make__DownlinkConfigCommonSIB__Type {
    DownlinkConfigCommonSIB__frequencyInfoDL : FrequencyInfoDL_SIB__Type ;
    DownlinkConfigCommonSIB__initialDownlinkBWP : BWP_DownlinkCommon__Type ;
    DownlinkConfigCommonSIB__bcch_Config : BCCH_Config__Type ;
    DownlinkConfigCommonSIB__pcch_Config : PCCH_Config__Type ;
    DownlinkConfigCommonSIB__ext0 : option DownlinkConfigCommonSIB__ext0__Type ;
}.
Definition DownlinkConfigCommonSIB__root_list : list seq_elem := (
 Nor FrequencyInfoDL_SIB__Type FrequencyInfoDL_SIB__cond ::
 Nor BWP_DownlinkCommon__Type BWP_DownlinkCommon__cond ::
 Nor BCCH_Config__Type BCCH_Config__cond ::
 Nor PCCH_Config__Type PCCH_Config__cond ::
 nil).
Definition DownlinkConfigCommonSIB__ext_list : list typ := (
  typ_cons DownlinkConfigCommonSIB__ext0__Type DownlinkConfigCommonSIB__ext0__cond ::
  nil).
Definition DownlinkConfigCommonSIB__cond (z : DownlinkConfigCommonSIB__Type) := 
(  FrequencyInfoDL_SIB__cond (DownlinkConfigCommonSIB__frequencyInfoDL z) /\
  BWP_DownlinkCommon__cond (DownlinkConfigCommonSIB__initialDownlinkBWP z) /\
  BCCH_Config__cond (DownlinkConfigCommonSIB__bcch_Config z) /\
  PCCH_Config__cond (DownlinkConfigCommonSIB__pcch_Config z) /\
  True) /\ 
(  opt_cond DownlinkConfigCommonSIB__ext0__cond (DownlinkConfigCommonSIB__ext0 z) /\
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

Definition DownlinkConfigCommonSIB__ext0O__Format_Type := Eval cbn in seq_format_prod DownlinkConfigCommonSIB__ext0O__list.
Definition DownlinkConfigCommonSIB__ext0O__Format_list : DownlinkConfigCommonSIB__ext0O__Format_Type :=
  (PEI_Config_r17__Format, (BWP_DownlinkCommon__Format, unit_format)).
Definition DownlinkConfigCommonSIB__ext0O__list__Format := (*Eval compute in *) seq_format DownlinkConfigCommonSIB__ext0O__list DownlinkConfigCommonSIB__ext0O__Format_list.
Definition DownlinkConfigCommonSIB__ext0O__F1 z :=
  (DownlinkConfigCommonSIB__ext0O__pei_Config_r17 z, (DownlinkConfigCommonSIB__ext0O__initialDownlinkBWP_RedCap_r17 z, tt)).
Definition DownlinkConfigCommonSIB__ext0O__F2 (y : seq_type DownlinkConfigCommonSIB__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DownlinkConfigCommonSIB__ext0O__Type i0 i1
  end.
Lemma DownlinkConfigCommonSIB__ext0O__F1F2_cond (z : DownlinkConfigCommonSIB__ext0O__Type)
  : DownlinkConfigCommonSIB__ext0O__cond z ->
  (seq_cond DownlinkConfigCommonSIB__ext0O__list (DownlinkConfigCommonSIB__ext0O__F1 z)).
intro H. unfold DownlinkConfigCommonSIB__ext0O__cond in H. simpl. auto. Qed.
Lemma DownlinkConfigCommonSIB__ext0O__F1F2_cond2 (z : DownlinkConfigCommonSIB__ext0O__Type)
 : DownlinkConfigCommonSIB__ext0O__F2 (DownlinkConfigCommonSIB__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DownlinkConfigCommonSIB__ext0O__F2F1_cond (y : seq_type DownlinkConfigCommonSIB__ext0O__list)
  : seq_cond DownlinkConfigCommonSIB__ext0O__list y ->
 (DownlinkConfigCommonSIB__ext0O__cond (DownlinkConfigCommonSIB__ext0O__F2 y)) /\  DownlinkConfigCommonSIB__ext0O__F1 (DownlinkConfigCommonSIB__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DownlinkConfigCommonSIB__ext0O__cond. simpl in *. auto.
 - simpl. unfold DownlinkConfigCommonSIB__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DownlinkConfigCommonSIB__ext0O__Format : T_Format DownlinkConfigCommonSIB__ext0O__Type DownlinkConfigCommonSIB__ext0O__cond :=
        proj2_format  DownlinkConfigCommonSIB__ext0O__cond DownlinkConfigCommonSIB__ext0O__list__Format
    DownlinkConfigCommonSIB__ext0O__F1 DownlinkConfigCommonSIB__ext0O__F2 DownlinkConfigCommonSIB__ext0O__F1F2_cond  DownlinkConfigCommonSIB__ext0O__F1F2_cond2 DownlinkConfigCommonSIB__ext0O__F2F1_cond.
Opaque DownlinkConfigCommonSIB__ext0O__cond DownlinkConfigCommonSIB__ext0O__Format.

Definition DownlinkConfigCommonSIB__ext0__check_all_none (b : DownlinkConfigCommonSIB__ext0O__Type) : bool :=
match b with 
  | make__DownlinkConfigCommonSIB__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition DownlinkConfigCommonSIB__ext0__Format : T_Format DownlinkConfigCommonSIB__ext0__Type DownlinkConfigCommonSIB__ext0__cond :=
  restrict_add_format DownlinkConfigCommonSIB__ext0__check_all_none DownlinkConfigCommonSIB__ext0O__Format.

Opaque DownlinkConfigCommonSIB__ext0__cond DownlinkConfigCommonSIB__ext0__Format.


Definition DownlinkConfigCommonSIB__root_Format_Type := Eval cbn in seq_format_prod DownlinkConfigCommonSIB__root_list.
Definition DownlinkConfigCommonSIB__root_Format_list : DownlinkConfigCommonSIB__root_Format_Type :=
  (FrequencyInfoDL_SIB__Format, (BWP_DownlinkCommon__Format, (BCCH_Config__Format, (PCCH_Config__Format, unit_format)))).

Definition DownlinkConfigCommonSIB__ext_Format_Type := Eval cbn in get_formats DownlinkConfigCommonSIB__ext_list.
Definition DownlinkConfigCommonSIB__ext_Format_list : DownlinkConfigCommonSIB__ext_Format_Type :=
  (DownlinkConfigCommonSIB__ext0__Format, unit__Format).

Definition DownlinkConfigCommonSIB__list_type : Set := (seq_type DownlinkConfigCommonSIB__root_list) * (seq_ext_type DownlinkConfigCommonSIB__ext_list).
Definition DownlinkConfigCommonSIB__list_cond (z : DownlinkConfigCommonSIB__list_type) : Prop :=
        (seq_cond DownlinkConfigCommonSIB__root_list (fst z)) /\ (seq_ext_cond DownlinkConfigCommonSIB__ext_list (snd z)).
Definition DownlinkConfigCommonSIB__list_format : T_Format DownlinkConfigCommonSIB__list_type DownlinkConfigCommonSIB__list_cond :=
 (* Eval compute in *) seq_ext_format DownlinkConfigCommonSIB__root_list DownlinkConfigCommonSIB__root_Format_list DownlinkConfigCommonSIB__ext_list DownlinkConfigCommonSIB__ext_Format_list.

Opaque DownlinkConfigCommonSIB__list_format.
Definition DownlinkConfigCommonSIB__F1 (z : DownlinkConfigCommonSIB__Type) : DownlinkConfigCommonSIB__list_type :=
  (((DownlinkConfigCommonSIB__frequencyInfoDL z, (DownlinkConfigCommonSIB__initialDownlinkBWP z, (DownlinkConfigCommonSIB__bcch_Config z, (DownlinkConfigCommonSIB__pcch_Config z, tt))))), (
(DownlinkConfigCommonSIB__ext0 z, tt))).
Definition DownlinkConfigCommonSIB__F2 (y : DownlinkConfigCommonSIB__list_type) : DownlinkConfigCommonSIB__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__DownlinkConfigCommonSIB__Type j0 j1 j2 j3 i0
  end.
Definition DownlinkConfigCommonSIB__helper1 : (forall a : DownlinkConfigCommonSIB__Type, DownlinkConfigCommonSIB__cond a -> DownlinkConfigCommonSIB__list_cond (DownlinkConfigCommonSIB__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DownlinkConfigCommonSIB__helper2 : (forall a : DownlinkConfigCommonSIB__Type, DownlinkConfigCommonSIB__F2 (DownlinkConfigCommonSIB__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DownlinkConfigCommonSIB__helper3 : (forall b : DownlinkConfigCommonSIB__list_type, DownlinkConfigCommonSIB__list_cond b -> DownlinkConfigCommonSIB__cond (DownlinkConfigCommonSIB__F2 b) /\ DownlinkConfigCommonSIB__F1 (DownlinkConfigCommonSIB__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DownlinkConfigCommonSIB__cond, DownlinkConfigCommonSIB__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DownlinkConfigCommonSIB__Format : T_Format DownlinkConfigCommonSIB__Type DownlinkConfigCommonSIB__cond :=
 proj2_format DownlinkConfigCommonSIB__cond DownlinkConfigCommonSIB__list_format  DownlinkConfigCommonSIB__F1 DownlinkConfigCommonSIB__F2 DownlinkConfigCommonSIB__helper1 DownlinkConfigCommonSIB__helper2 DownlinkConfigCommonSIB__helper3.

Opaque DownlinkConfigCommonSIB__cond DownlinkConfigCommonSIB__Format.

