Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FrequencyInfoDL.

Opaque FrequencyInfoDL__cond FrequencyInfoDL__Format.

Require Import NR.BWP_DownlinkCommon.

Opaque BWP_DownlinkCommon__cond BWP_DownlinkCommon__Format.

Require Import NR.BWP_DownlinkCommon.

Opaque BWP_DownlinkCommon__cond BWP_DownlinkCommon__Format.

Record DownlinkConfigCommon__ext0O__Type : Set :=
  make__DownlinkConfigCommon__ext0O__Type {
    DownlinkConfigCommon__ext0O__initialDownlinkBWP_RedCap_r17 : option BWP_DownlinkCommon__Type ;
}.
Definition DownlinkConfigCommon__ext0O__list := (
 Opt BWP_DownlinkCommon__Type BWP_DownlinkCommon__cond ::
 nil).
Definition DownlinkConfigCommon__ext0O__cond z := 
  opt_cond BWP_DownlinkCommon__cond (DownlinkConfigCommon__ext0O__initialDownlinkBWP_RedCap_r17 z) /\
  True.

Definition DownlinkConfigCommon__ext0__Type := DownlinkConfigCommon__ext0O__Type.
Definition DownlinkConfigCommon__ext0__cond := DownlinkConfigCommon__ext0O__cond.

Record DownlinkConfigCommon__Type : Set :=
  make__DownlinkConfigCommon__Type {
    DownlinkConfigCommon__frequencyInfoDL : option FrequencyInfoDL__Type ;
    DownlinkConfigCommon__initialDownlinkBWP : option BWP_DownlinkCommon__Type ;
    DownlinkConfigCommon__ext0 : option DownlinkConfigCommon__ext0__Type ;
}.
Definition DownlinkConfigCommon__root_list : list seq_elem := (
 Opt FrequencyInfoDL__Type FrequencyInfoDL__cond ::
 Opt BWP_DownlinkCommon__Type BWP_DownlinkCommon__cond ::
 nil).
Definition DownlinkConfigCommon__ext_list : list typ := (
  typ_cons DownlinkConfigCommon__ext0__Type DownlinkConfigCommon__ext0__cond ::
  nil).
Definition DownlinkConfigCommon__cond (z : DownlinkConfigCommon__Type) := 
(  opt_cond FrequencyInfoDL__cond (DownlinkConfigCommon__frequencyInfoDL z) /\
  opt_cond BWP_DownlinkCommon__cond (DownlinkConfigCommon__initialDownlinkBWP z) /\
  True) /\ 
(  opt_cond DownlinkConfigCommon__ext0__cond (DownlinkConfigCommon__ext0 z) /\
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

Definition DownlinkConfigCommon__ext0O__Format_Type := Eval cbn in seq_format_prod DownlinkConfigCommon__ext0O__list.
Definition DownlinkConfigCommon__ext0O__Format_list : DownlinkConfigCommon__ext0O__Format_Type :=
  (BWP_DownlinkCommon__Format, unit_format).
Definition DownlinkConfigCommon__ext0O__list__Format := (*Eval compute in *) seq_format DownlinkConfigCommon__ext0O__list DownlinkConfigCommon__ext0O__Format_list.
Definition DownlinkConfigCommon__ext0O__F1 z :=
  (DownlinkConfigCommon__ext0O__initialDownlinkBWP_RedCap_r17 z, tt).
Definition DownlinkConfigCommon__ext0O__F2 (y : seq_type DownlinkConfigCommon__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__DownlinkConfigCommon__ext0O__Type i0
  end.
Lemma DownlinkConfigCommon__ext0O__F1F2_cond (z : DownlinkConfigCommon__ext0O__Type)
  : DownlinkConfigCommon__ext0O__cond z ->
  (seq_cond DownlinkConfigCommon__ext0O__list (DownlinkConfigCommon__ext0O__F1 z)).
intro H. unfold DownlinkConfigCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma DownlinkConfigCommon__ext0O__F1F2_cond2 (z : DownlinkConfigCommon__ext0O__Type)
 : DownlinkConfigCommon__ext0O__F2 (DownlinkConfigCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DownlinkConfigCommon__ext0O__F2F1_cond (y : seq_type DownlinkConfigCommon__ext0O__list)
  : seq_cond DownlinkConfigCommon__ext0O__list y ->
 (DownlinkConfigCommon__ext0O__cond (DownlinkConfigCommon__ext0O__F2 y)) /\  DownlinkConfigCommon__ext0O__F1 (DownlinkConfigCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DownlinkConfigCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold DownlinkConfigCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DownlinkConfigCommon__ext0O__Format : T_Format DownlinkConfigCommon__ext0O__Type DownlinkConfigCommon__ext0O__cond :=
        proj2_format  DownlinkConfigCommon__ext0O__cond DownlinkConfigCommon__ext0O__list__Format
    DownlinkConfigCommon__ext0O__F1 DownlinkConfigCommon__ext0O__F2 DownlinkConfigCommon__ext0O__F1F2_cond  DownlinkConfigCommon__ext0O__F1F2_cond2 DownlinkConfigCommon__ext0O__F2F1_cond.
Opaque DownlinkConfigCommon__ext0O__cond DownlinkConfigCommon__ext0O__Format.

Definition DownlinkConfigCommon__ext0__check_all_none (b : DownlinkConfigCommon__ext0O__Type) : bool :=
match b with 
  | make__DownlinkConfigCommon__ext0O__Type None  => false 
  | _ => true 
 end.
Definition DownlinkConfigCommon__ext0__Format : T_Format DownlinkConfigCommon__ext0__Type DownlinkConfigCommon__ext0__cond :=
  restrict_add_format DownlinkConfigCommon__ext0__check_all_none DownlinkConfigCommon__ext0O__Format.

Opaque DownlinkConfigCommon__ext0__cond DownlinkConfigCommon__ext0__Format.


Definition DownlinkConfigCommon__root_Format_Type := Eval cbn in seq_format_prod DownlinkConfigCommon__root_list.
Definition DownlinkConfigCommon__root_Format_list : DownlinkConfigCommon__root_Format_Type :=
  (FrequencyInfoDL__Format, (BWP_DownlinkCommon__Format, unit_format)).

Definition DownlinkConfigCommon__ext_Format_Type := Eval cbn in get_formats DownlinkConfigCommon__ext_list.
Definition DownlinkConfigCommon__ext_Format_list : DownlinkConfigCommon__ext_Format_Type :=
  (DownlinkConfigCommon__ext0__Format, unit__Format).

Definition DownlinkConfigCommon__list_type : Set := (seq_type DownlinkConfigCommon__root_list) * (seq_ext_type DownlinkConfigCommon__ext_list).
Definition DownlinkConfigCommon__list_cond (z : DownlinkConfigCommon__list_type) : Prop :=
        (seq_cond DownlinkConfigCommon__root_list (fst z)) /\ (seq_ext_cond DownlinkConfigCommon__ext_list (snd z)).
Definition DownlinkConfigCommon__list_format : T_Format DownlinkConfigCommon__list_type DownlinkConfigCommon__list_cond :=
 (* Eval compute in *) seq_ext_format DownlinkConfigCommon__root_list DownlinkConfigCommon__root_Format_list DownlinkConfigCommon__ext_list DownlinkConfigCommon__ext_Format_list.

Opaque DownlinkConfigCommon__list_format.
Definition DownlinkConfigCommon__F1 (z : DownlinkConfigCommon__Type) : DownlinkConfigCommon__list_type :=
  (((DownlinkConfigCommon__frequencyInfoDL z, (DownlinkConfigCommon__initialDownlinkBWP z, tt))), (
(DownlinkConfigCommon__ext0 z, tt))).
Definition DownlinkConfigCommon__F2 (y : DownlinkConfigCommon__list_type) : DownlinkConfigCommon__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__DownlinkConfigCommon__Type j0 j1 i0
  end.
Definition DownlinkConfigCommon__helper1 : (forall a : DownlinkConfigCommon__Type, DownlinkConfigCommon__cond a -> DownlinkConfigCommon__list_cond (DownlinkConfigCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DownlinkConfigCommon__helper2 : (forall a : DownlinkConfigCommon__Type, DownlinkConfigCommon__F2 (DownlinkConfigCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DownlinkConfigCommon__helper3 : (forall b : DownlinkConfigCommon__list_type, DownlinkConfigCommon__list_cond b -> DownlinkConfigCommon__cond (DownlinkConfigCommon__F2 b) /\ DownlinkConfigCommon__F1 (DownlinkConfigCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DownlinkConfigCommon__cond, DownlinkConfigCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DownlinkConfigCommon__Format : T_Format DownlinkConfigCommon__Type DownlinkConfigCommon__cond :=
 proj2_format DownlinkConfigCommon__cond DownlinkConfigCommon__list_format  DownlinkConfigCommon__F1 DownlinkConfigCommon__F2 DownlinkConfigCommon__helper1 DownlinkConfigCommon__helper2 DownlinkConfigCommon__helper3.

Opaque DownlinkConfigCommon__cond DownlinkConfigCommon__Format.

