Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CFRA.

Opaque CFRA__cond CFRA__Format.

Require Import NR.RA_Prioritization.

Opaque RA_Prioritization__cond RA_Prioritization__Format.

Require Import NR.RA_Prioritization.

Opaque RA_Prioritization__cond RA_Prioritization__Format.

Require Import NR.CFRA_TwoStep_r16.

Opaque CFRA_TwoStep_r16__cond CFRA_TwoStep_r16__Format.

Record RACH_ConfigDedicated__ext0O__Type : Set :=
  make__RACH_ConfigDedicated__ext0O__Type {
    RACH_ConfigDedicated__ext0O__ra_PrioritizationTwoStep_r16 : option RA_Prioritization__Type ;
    RACH_ConfigDedicated__ext0O__cfra_TwoStep_r16 : option CFRA_TwoStep_r16__Type ;
}.
Definition RACH_ConfigDedicated__ext0O__list := (
 Opt RA_Prioritization__Type RA_Prioritization__cond ::
 Opt CFRA_TwoStep_r16__Type CFRA_TwoStep_r16__cond ::
 nil).
Definition RACH_ConfigDedicated__ext0O__cond z := 
  opt_cond RA_Prioritization__cond (RACH_ConfigDedicated__ext0O__ra_PrioritizationTwoStep_r16 z) /\
  opt_cond CFRA_TwoStep_r16__cond (RACH_ConfigDedicated__ext0O__cfra_TwoStep_r16 z) /\
  True.

Definition RACH_ConfigDedicated__ext0__Type := RACH_ConfigDedicated__ext0O__Type.
Definition RACH_ConfigDedicated__ext0__cond := RACH_ConfigDedicated__ext0O__cond.

Record RACH_ConfigDedicated__Type : Set :=
  make__RACH_ConfigDedicated__Type {
    RACH_ConfigDedicated__cfra : option CFRA__Type ;
    RACH_ConfigDedicated__ra_Prioritization : option RA_Prioritization__Type ;
    RACH_ConfigDedicated__ext0 : option RACH_ConfigDedicated__ext0__Type ;
}.
Definition RACH_ConfigDedicated__root_list : list seq_elem := (
 Opt CFRA__Type CFRA__cond ::
 Opt RA_Prioritization__Type RA_Prioritization__cond ::
 nil).
Definition RACH_ConfigDedicated__ext_list : list typ := (
  typ_cons RACH_ConfigDedicated__ext0__Type RACH_ConfigDedicated__ext0__cond ::
  nil).
Definition RACH_ConfigDedicated__cond (z : RACH_ConfigDedicated__Type) := 
(  opt_cond CFRA__cond (RACH_ConfigDedicated__cfra z) /\
  opt_cond RA_Prioritization__cond (RACH_ConfigDedicated__ra_Prioritization z) /\
  True) /\ 
(  opt_cond RACH_ConfigDedicated__ext0__cond (RACH_ConfigDedicated__ext0 z) /\
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

Definition RACH_ConfigDedicated__ext0O__Format_Type := Eval cbn in seq_format_prod RACH_ConfigDedicated__ext0O__list.
Definition RACH_ConfigDedicated__ext0O__Format_list : RACH_ConfigDedicated__ext0O__Format_Type :=
  (RA_Prioritization__Format, (CFRA_TwoStep_r16__Format, unit_format)).
Definition RACH_ConfigDedicated__ext0O__list__Format := (*Eval compute in *) seq_format RACH_ConfigDedicated__ext0O__list RACH_ConfigDedicated__ext0O__Format_list.
Definition RACH_ConfigDedicated__ext0O__F1 z :=
  (RACH_ConfigDedicated__ext0O__ra_PrioritizationTwoStep_r16 z, (RACH_ConfigDedicated__ext0O__cfra_TwoStep_r16 z, tt)).
Definition RACH_ConfigDedicated__ext0O__F2 (y : seq_type RACH_ConfigDedicated__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RACH_ConfigDedicated__ext0O__Type i0 i1
  end.
Lemma RACH_ConfigDedicated__ext0O__F1F2_cond (z : RACH_ConfigDedicated__ext0O__Type)
  : RACH_ConfigDedicated__ext0O__cond z ->
  (seq_cond RACH_ConfigDedicated__ext0O__list (RACH_ConfigDedicated__ext0O__F1 z)).
intro H. unfold RACH_ConfigDedicated__ext0O__cond in H. simpl. auto. Qed.
Lemma RACH_ConfigDedicated__ext0O__F1F2_cond2 (z : RACH_ConfigDedicated__ext0O__Type)
 : RACH_ConfigDedicated__ext0O__F2 (RACH_ConfigDedicated__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RACH_ConfigDedicated__ext0O__F2F1_cond (y : seq_type RACH_ConfigDedicated__ext0O__list)
  : seq_cond RACH_ConfigDedicated__ext0O__list y ->
 (RACH_ConfigDedicated__ext0O__cond (RACH_ConfigDedicated__ext0O__F2 y)) /\  RACH_ConfigDedicated__ext0O__F1 (RACH_ConfigDedicated__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RACH_ConfigDedicated__ext0O__cond. simpl in *. auto.
 - simpl. unfold RACH_ConfigDedicated__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RACH_ConfigDedicated__ext0O__Format : T_Format RACH_ConfigDedicated__ext0O__Type RACH_ConfigDedicated__ext0O__cond :=
        proj2_format  RACH_ConfigDedicated__ext0O__cond RACH_ConfigDedicated__ext0O__list__Format
    RACH_ConfigDedicated__ext0O__F1 RACH_ConfigDedicated__ext0O__F2 RACH_ConfigDedicated__ext0O__F1F2_cond  RACH_ConfigDedicated__ext0O__F1F2_cond2 RACH_ConfigDedicated__ext0O__F2F1_cond.
Opaque RACH_ConfigDedicated__ext0O__cond RACH_ConfigDedicated__ext0O__Format.

Definition RACH_ConfigDedicated__ext0__check_all_none (b : RACH_ConfigDedicated__ext0O__Type) : bool :=
match b with 
  | make__RACH_ConfigDedicated__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition RACH_ConfigDedicated__ext0__Format : T_Format RACH_ConfigDedicated__ext0__Type RACH_ConfigDedicated__ext0__cond :=
  restrict_add_format RACH_ConfigDedicated__ext0__check_all_none RACH_ConfigDedicated__ext0O__Format.

Opaque RACH_ConfigDedicated__ext0__cond RACH_ConfigDedicated__ext0__Format.


Definition RACH_ConfigDedicated__root_Format_Type := Eval cbn in seq_format_prod RACH_ConfigDedicated__root_list.
Definition RACH_ConfigDedicated__root_Format_list : RACH_ConfigDedicated__root_Format_Type :=
  (CFRA__Format, (RA_Prioritization__Format, unit_format)).

Definition RACH_ConfigDedicated__ext_Format_Type := Eval cbn in get_formats RACH_ConfigDedicated__ext_list.
Definition RACH_ConfigDedicated__ext_Format_list : RACH_ConfigDedicated__ext_Format_Type :=
  (RACH_ConfigDedicated__ext0__Format, unit__Format).

Definition RACH_ConfigDedicated__list_type : Set := (seq_type RACH_ConfigDedicated__root_list) * (seq_ext_type RACH_ConfigDedicated__ext_list).
Definition RACH_ConfigDedicated__list_cond (z : RACH_ConfigDedicated__list_type) : Prop :=
        (seq_cond RACH_ConfigDedicated__root_list (fst z)) /\ (seq_ext_cond RACH_ConfigDedicated__ext_list (snd z)).
Definition RACH_ConfigDedicated__list_format : T_Format RACH_ConfigDedicated__list_type RACH_ConfigDedicated__list_cond :=
 (* Eval compute in *) seq_ext_format RACH_ConfigDedicated__root_list RACH_ConfigDedicated__root_Format_list RACH_ConfigDedicated__ext_list RACH_ConfigDedicated__ext_Format_list.

Opaque RACH_ConfigDedicated__list_format.
Definition RACH_ConfigDedicated__F1 (z : RACH_ConfigDedicated__Type) : RACH_ConfigDedicated__list_type :=
  (((RACH_ConfigDedicated__cfra z, (RACH_ConfigDedicated__ra_Prioritization z, tt))), (
(RACH_ConfigDedicated__ext0 z, tt))).
Definition RACH_ConfigDedicated__F2 (y : RACH_ConfigDedicated__list_type) : RACH_ConfigDedicated__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__RACH_ConfigDedicated__Type j0 j1 i0
  end.
Definition RACH_ConfigDedicated__helper1 : (forall a : RACH_ConfigDedicated__Type, RACH_ConfigDedicated__cond a -> RACH_ConfigDedicated__list_cond (RACH_ConfigDedicated__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RACH_ConfigDedicated__helper2 : (forall a : RACH_ConfigDedicated__Type, RACH_ConfigDedicated__F2 (RACH_ConfigDedicated__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RACH_ConfigDedicated__helper3 : (forall b : RACH_ConfigDedicated__list_type, RACH_ConfigDedicated__list_cond b -> RACH_ConfigDedicated__cond (RACH_ConfigDedicated__F2 b) /\ RACH_ConfigDedicated__F1 (RACH_ConfigDedicated__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RACH_ConfigDedicated__cond, RACH_ConfigDedicated__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RACH_ConfigDedicated__Format : T_Format RACH_ConfigDedicated__Type RACH_ConfigDedicated__cond :=
 proj2_format RACH_ConfigDedicated__cond RACH_ConfigDedicated__list_format  RACH_ConfigDedicated__F1 RACH_ConfigDedicated__F2 RACH_ConfigDedicated__helper1 RACH_ConfigDedicated__helper2 RACH_ConfigDedicated__helper3.

Opaque RACH_ConfigDedicated__cond RACH_ConfigDedicated__Format.

