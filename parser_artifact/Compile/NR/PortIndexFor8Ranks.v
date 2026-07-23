Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PortIndex8.

Opaque PortIndex8__cond PortIndex8__Format.

Require Import NR.PortIndex8.

Opaque PortIndex8__cond PortIndex8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank2_8__Type := list PortIndex8__Type.

Definition PortIndexFor8Ranks__portIndex8__rank2_8__cond (z : PortIndexFor8Ranks__portIndex8__rank2_8__Type) := (list_and PortIndex8__cond z) /\ (length z = Z.to_nat 2).

Require Import NR.PortIndex8.

Opaque PortIndex8__cond PortIndex8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank3_8__Type := list PortIndex8__Type.

Definition PortIndexFor8Ranks__portIndex8__rank3_8__cond (z : PortIndexFor8Ranks__portIndex8__rank3_8__Type) := (list_and PortIndex8__cond z) /\ (length z = Z.to_nat 3).

Require Import NR.PortIndex8.

Opaque PortIndex8__cond PortIndex8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank4_8__Type := list PortIndex8__Type.

Definition PortIndexFor8Ranks__portIndex8__rank4_8__cond (z : PortIndexFor8Ranks__portIndex8__rank4_8__Type) := (list_and PortIndex8__cond z) /\ (length z = Z.to_nat 4).

Require Import NR.PortIndex8.

Opaque PortIndex8__cond PortIndex8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank5_8__Type := list PortIndex8__Type.

Definition PortIndexFor8Ranks__portIndex8__rank5_8__cond (z : PortIndexFor8Ranks__portIndex8__rank5_8__Type) := (list_and PortIndex8__cond z) /\ (length z = Z.to_nat 5).

Require Import NR.PortIndex8.

Opaque PortIndex8__cond PortIndex8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank6_8__Type := list PortIndex8__Type.

Definition PortIndexFor8Ranks__portIndex8__rank6_8__cond (z : PortIndexFor8Ranks__portIndex8__rank6_8__Type) := (list_and PortIndex8__cond z) /\ (length z = Z.to_nat 6).

Require Import NR.PortIndex8.

Opaque PortIndex8__cond PortIndex8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank7_8__Type := list PortIndex8__Type.

Definition PortIndexFor8Ranks__portIndex8__rank7_8__cond (z : PortIndexFor8Ranks__portIndex8__rank7_8__Type) := (list_and PortIndex8__cond z) /\ (length z = Z.to_nat 7).

Require Import NR.PortIndex8.

Opaque PortIndex8__cond PortIndex8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank8_8__Type := list PortIndex8__Type.

Definition PortIndexFor8Ranks__portIndex8__rank8_8__cond (z : PortIndexFor8Ranks__portIndex8__rank8_8__Type) := (list_and PortIndex8__cond z) /\ (length z = Z.to_nat 8).

Record PortIndexFor8Ranks__portIndex8__Type : Set :=
  make__PortIndexFor8Ranks__portIndex8__Type {
    PortIndexFor8Ranks__portIndex8__rank1_8 : option PortIndex8__Type ;
    PortIndexFor8Ranks__portIndex8__rank2_8 : option PortIndexFor8Ranks__portIndex8__rank2_8__Type ;
    PortIndexFor8Ranks__portIndex8__rank3_8 : option PortIndexFor8Ranks__portIndex8__rank3_8__Type ;
    PortIndexFor8Ranks__portIndex8__rank4_8 : option PortIndexFor8Ranks__portIndex8__rank4_8__Type ;
    PortIndexFor8Ranks__portIndex8__rank5_8 : option PortIndexFor8Ranks__portIndex8__rank5_8__Type ;
    PortIndexFor8Ranks__portIndex8__rank6_8 : option PortIndexFor8Ranks__portIndex8__rank6_8__Type ;
    PortIndexFor8Ranks__portIndex8__rank7_8 : option PortIndexFor8Ranks__portIndex8__rank7_8__Type ;
    PortIndexFor8Ranks__portIndex8__rank8_8 : option PortIndexFor8Ranks__portIndex8__rank8_8__Type ;
}.
Definition PortIndexFor8Ranks__portIndex8__list := (
 Opt PortIndex8__Type PortIndex8__cond ::
 Opt PortIndexFor8Ranks__portIndex8__rank2_8__Type PortIndexFor8Ranks__portIndex8__rank2_8__cond ::
 Opt PortIndexFor8Ranks__portIndex8__rank3_8__Type PortIndexFor8Ranks__portIndex8__rank3_8__cond ::
 Opt PortIndexFor8Ranks__portIndex8__rank4_8__Type PortIndexFor8Ranks__portIndex8__rank4_8__cond ::
 Opt PortIndexFor8Ranks__portIndex8__rank5_8__Type PortIndexFor8Ranks__portIndex8__rank5_8__cond ::
 Opt PortIndexFor8Ranks__portIndex8__rank6_8__Type PortIndexFor8Ranks__portIndex8__rank6_8__cond ::
 Opt PortIndexFor8Ranks__portIndex8__rank7_8__Type PortIndexFor8Ranks__portIndex8__rank7_8__cond ::
 Opt PortIndexFor8Ranks__portIndex8__rank8_8__Type PortIndexFor8Ranks__portIndex8__rank8_8__cond ::
 nil).
Definition PortIndexFor8Ranks__portIndex8__cond z := 
  opt_cond PortIndex8__cond (PortIndexFor8Ranks__portIndex8__rank1_8 z) /\
  opt_cond PortIndexFor8Ranks__portIndex8__rank2_8__cond (PortIndexFor8Ranks__portIndex8__rank2_8 z) /\
  opt_cond PortIndexFor8Ranks__portIndex8__rank3_8__cond (PortIndexFor8Ranks__portIndex8__rank3_8 z) /\
  opt_cond PortIndexFor8Ranks__portIndex8__rank4_8__cond (PortIndexFor8Ranks__portIndex8__rank4_8 z) /\
  opt_cond PortIndexFor8Ranks__portIndex8__rank5_8__cond (PortIndexFor8Ranks__portIndex8__rank5_8 z) /\
  opt_cond PortIndexFor8Ranks__portIndex8__rank6_8__cond (PortIndexFor8Ranks__portIndex8__rank6_8 z) /\
  opt_cond PortIndexFor8Ranks__portIndex8__rank7_8__cond (PortIndexFor8Ranks__portIndex8__rank7_8 z) /\
  opt_cond PortIndexFor8Ranks__portIndex8__rank8_8__cond (PortIndexFor8Ranks__portIndex8__rank8_8 z) /\
  True.

Require Import NR.PortIndex4.

Opaque PortIndex4__cond PortIndex4__Format.

Require Import NR.PortIndex4.

Opaque PortIndex4__cond PortIndex4__Format.

Definition PortIndexFor8Ranks__portIndex4__rank2_4__Type := list PortIndex4__Type.

Definition PortIndexFor8Ranks__portIndex4__rank2_4__cond (z : PortIndexFor8Ranks__portIndex4__rank2_4__Type) := (list_and PortIndex4__cond z) /\ (length z = Z.to_nat 2).

Require Import NR.PortIndex4.

Opaque PortIndex4__cond PortIndex4__Format.

Definition PortIndexFor8Ranks__portIndex4__rank3_4__Type := list PortIndex4__Type.

Definition PortIndexFor8Ranks__portIndex4__rank3_4__cond (z : PortIndexFor8Ranks__portIndex4__rank3_4__Type) := (list_and PortIndex4__cond z) /\ (length z = Z.to_nat 3).

Require Import NR.PortIndex4.

Opaque PortIndex4__cond PortIndex4__Format.

Definition PortIndexFor8Ranks__portIndex4__rank4_4__Type := list PortIndex4__Type.

Definition PortIndexFor8Ranks__portIndex4__rank4_4__cond (z : PortIndexFor8Ranks__portIndex4__rank4_4__Type) := (list_and PortIndex4__cond z) /\ (length z = Z.to_nat 4).

Record PortIndexFor8Ranks__portIndex4__Type : Set :=
  make__PortIndexFor8Ranks__portIndex4__Type {
    PortIndexFor8Ranks__portIndex4__rank1_4 : option PortIndex4__Type ;
    PortIndexFor8Ranks__portIndex4__rank2_4 : option PortIndexFor8Ranks__portIndex4__rank2_4__Type ;
    PortIndexFor8Ranks__portIndex4__rank3_4 : option PortIndexFor8Ranks__portIndex4__rank3_4__Type ;
    PortIndexFor8Ranks__portIndex4__rank4_4 : option PortIndexFor8Ranks__portIndex4__rank4_4__Type ;
}.
Definition PortIndexFor8Ranks__portIndex4__list := (
 Opt PortIndex4__Type PortIndex4__cond ::
 Opt PortIndexFor8Ranks__portIndex4__rank2_4__Type PortIndexFor8Ranks__portIndex4__rank2_4__cond ::
 Opt PortIndexFor8Ranks__portIndex4__rank3_4__Type PortIndexFor8Ranks__portIndex4__rank3_4__cond ::
 Opt PortIndexFor8Ranks__portIndex4__rank4_4__Type PortIndexFor8Ranks__portIndex4__rank4_4__cond ::
 nil).
Definition PortIndexFor8Ranks__portIndex4__cond z := 
  opt_cond PortIndex4__cond (PortIndexFor8Ranks__portIndex4__rank1_4 z) /\
  opt_cond PortIndexFor8Ranks__portIndex4__rank2_4__cond (PortIndexFor8Ranks__portIndex4__rank2_4 z) /\
  opt_cond PortIndexFor8Ranks__portIndex4__rank3_4__cond (PortIndexFor8Ranks__portIndex4__rank3_4 z) /\
  opt_cond PortIndexFor8Ranks__portIndex4__rank4_4__cond (PortIndexFor8Ranks__portIndex4__rank4_4 z) /\
  True.

Require Import NR.PortIndex2.

Opaque PortIndex2__cond PortIndex2__Format.

Require Import NR.PortIndex2.

Opaque PortIndex2__cond PortIndex2__Format.

Definition PortIndexFor8Ranks__portIndex2__rank2_2__Type := list PortIndex2__Type.

Definition PortIndexFor8Ranks__portIndex2__rank2_2__cond (z : PortIndexFor8Ranks__portIndex2__rank2_2__Type) := (list_and PortIndex2__cond z) /\ (length z = Z.to_nat 2).

Record PortIndexFor8Ranks__portIndex2__Type : Set :=
  make__PortIndexFor8Ranks__portIndex2__Type {
    PortIndexFor8Ranks__portIndex2__rank1_2 : option PortIndex2__Type ;
    PortIndexFor8Ranks__portIndex2__rank2_2 : option PortIndexFor8Ranks__portIndex2__rank2_2__Type ;
}.
Definition PortIndexFor8Ranks__portIndex2__list := (
 Opt PortIndex2__Type PortIndex2__cond ::
 Opt PortIndexFor8Ranks__portIndex2__rank2_2__Type PortIndexFor8Ranks__portIndex2__rank2_2__cond ::
 nil).
Definition PortIndexFor8Ranks__portIndex2__cond z := 
  opt_cond PortIndex2__cond (PortIndexFor8Ranks__portIndex2__rank1_2 z) /\
  opt_cond PortIndexFor8Ranks__portIndex2__rank2_2__cond (PortIndexFor8Ranks__portIndex2__rank2_2 z) /\
  True.


Inductive PortIndexFor8Ranks__Type : Set :=
  | PortIndexFor8Ranks__portIndex8 : PortIndexFor8Ranks__portIndex8__Type -> PortIndexFor8Ranks__Type
  | PortIndexFor8Ranks__portIndex4 : PortIndexFor8Ranks__portIndex4__Type -> PortIndexFor8Ranks__Type
  | PortIndexFor8Ranks__portIndex2 : PortIndexFor8Ranks__portIndex2__Type -> PortIndexFor8Ranks__Type
  | PortIndexFor8Ranks__portIndex1 : unit -> PortIndexFor8Ranks__Type
.
Definition PortIndexFor8Ranks__list : list typ := (
typ_cons PortIndexFor8Ranks__portIndex8__Type PortIndexFor8Ranks__portIndex8__cond ::
typ_cons PortIndexFor8Ranks__portIndex4__Type PortIndexFor8Ranks__portIndex4__cond ::
typ_cons PortIndexFor8Ranks__portIndex2__Type PortIndexFor8Ranks__portIndex2__cond ::
typ_cons unit (fun _ => True) ::
 nil).
Definition PortIndexFor8Ranks__cond (c : PortIndexFor8Ranks__Type) := 
  match c with
  | PortIndexFor8Ranks__portIndex8 t => PortIndexFor8Ranks__portIndex8__cond t 
  | PortIndexFor8Ranks__portIndex4 t => PortIndexFor8Ranks__portIndex4__cond t 
  | PortIndexFor8Ranks__portIndex2 t => PortIndexFor8Ranks__portIndex2__cond t 
  | PortIndexFor8Ranks__portIndex1 t => (fun _ => True) t 
  end.

Lemma PortIndexFor8Ranks__len_helper1 : to_bit_sz (length PortIndexFor8Ranks__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PortIndexFor8Ranks__len_helper2 : 2 <= length2 PortIndexFor8Ranks__list.
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
Definition PortIndexFor8Ranks__portIndex8__rank2_8__Format : T_Format PortIndexFor8Ranks__portIndex8__rank2_8__Type PortIndexFor8Ranks__portIndex8__rank2_8__cond := seq_of_fixed_format PortIndex8__Format 2.

Opaque PortIndexFor8Ranks__portIndex8__rank2_8__cond PortIndexFor8Ranks__portIndex8__rank2_8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank3_8__Format : T_Format PortIndexFor8Ranks__portIndex8__rank3_8__Type PortIndexFor8Ranks__portIndex8__rank3_8__cond := seq_of_fixed_format PortIndex8__Format 3.

Opaque PortIndexFor8Ranks__portIndex8__rank3_8__cond PortIndexFor8Ranks__portIndex8__rank3_8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank4_8__Format : T_Format PortIndexFor8Ranks__portIndex8__rank4_8__Type PortIndexFor8Ranks__portIndex8__rank4_8__cond := seq_of_fixed_format PortIndex8__Format 4.

Opaque PortIndexFor8Ranks__portIndex8__rank4_8__cond PortIndexFor8Ranks__portIndex8__rank4_8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank5_8__Format : T_Format PortIndexFor8Ranks__portIndex8__rank5_8__Type PortIndexFor8Ranks__portIndex8__rank5_8__cond := seq_of_fixed_format PortIndex8__Format 5.

Opaque PortIndexFor8Ranks__portIndex8__rank5_8__cond PortIndexFor8Ranks__portIndex8__rank5_8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank6_8__Format : T_Format PortIndexFor8Ranks__portIndex8__rank6_8__Type PortIndexFor8Ranks__portIndex8__rank6_8__cond := seq_of_fixed_format PortIndex8__Format 6.

Opaque PortIndexFor8Ranks__portIndex8__rank6_8__cond PortIndexFor8Ranks__portIndex8__rank6_8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank7_8__Format : T_Format PortIndexFor8Ranks__portIndex8__rank7_8__Type PortIndexFor8Ranks__portIndex8__rank7_8__cond := seq_of_fixed_format PortIndex8__Format 7.

Opaque PortIndexFor8Ranks__portIndex8__rank7_8__cond PortIndexFor8Ranks__portIndex8__rank7_8__Format.

Definition PortIndexFor8Ranks__portIndex8__rank8_8__Format : T_Format PortIndexFor8Ranks__portIndex8__rank8_8__Type PortIndexFor8Ranks__portIndex8__rank8_8__cond := seq_of_fixed_format PortIndex8__Format 8.

Opaque PortIndexFor8Ranks__portIndex8__rank8_8__cond PortIndexFor8Ranks__portIndex8__rank8_8__Format.


Definition PortIndexFor8Ranks__portIndex8__Format_Type := Eval cbn in seq_format_prod PortIndexFor8Ranks__portIndex8__list.
Definition PortIndexFor8Ranks__portIndex8__Format_list : PortIndexFor8Ranks__portIndex8__Format_Type :=
  (PortIndex8__Format, (PortIndexFor8Ranks__portIndex8__rank2_8__Format, (PortIndexFor8Ranks__portIndex8__rank3_8__Format, (PortIndexFor8Ranks__portIndex8__rank4_8__Format, (PortIndexFor8Ranks__portIndex8__rank5_8__Format, (PortIndexFor8Ranks__portIndex8__rank6_8__Format, (PortIndexFor8Ranks__portIndex8__rank7_8__Format, (PortIndexFor8Ranks__portIndex8__rank8_8__Format, unit_format)))))))).
Definition PortIndexFor8Ranks__portIndex8__list__Format := (*Eval compute in *) seq_format PortIndexFor8Ranks__portIndex8__list PortIndexFor8Ranks__portIndex8__Format_list.
Definition PortIndexFor8Ranks__portIndex8__F1 z :=
  (PortIndexFor8Ranks__portIndex8__rank1_8 z, (PortIndexFor8Ranks__portIndex8__rank2_8 z, (PortIndexFor8Ranks__portIndex8__rank3_8 z, (PortIndexFor8Ranks__portIndex8__rank4_8 z, (PortIndexFor8Ranks__portIndex8__rank5_8 z, (PortIndexFor8Ranks__portIndex8__rank6_8 z, (PortIndexFor8Ranks__portIndex8__rank7_8 z, (PortIndexFor8Ranks__portIndex8__rank8_8 z, tt)))))))).
Definition PortIndexFor8Ranks__portIndex8__F2 (y : seq_type PortIndexFor8Ranks__portIndex8__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__PortIndexFor8Ranks__portIndex8__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma PortIndexFor8Ranks__portIndex8__F1F2_cond (z : PortIndexFor8Ranks__portIndex8__Type)
  : PortIndexFor8Ranks__portIndex8__cond z ->
  (seq_cond PortIndexFor8Ranks__portIndex8__list (PortIndexFor8Ranks__portIndex8__F1 z)).
intro H. unfold PortIndexFor8Ranks__portIndex8__cond in H. simpl. auto. Qed.
Lemma PortIndexFor8Ranks__portIndex8__F1F2_cond2 (z : PortIndexFor8Ranks__portIndex8__Type)
 : PortIndexFor8Ranks__portIndex8__F2 (PortIndexFor8Ranks__portIndex8__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PortIndexFor8Ranks__portIndex8__F2F1_cond (y : seq_type PortIndexFor8Ranks__portIndex8__list)
  : seq_cond PortIndexFor8Ranks__portIndex8__list y ->
 (PortIndexFor8Ranks__portIndex8__cond (PortIndexFor8Ranks__portIndex8__F2 y)) /\  PortIndexFor8Ranks__portIndex8__F1 (PortIndexFor8Ranks__portIndex8__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PortIndexFor8Ranks__portIndex8__cond. simpl in *. auto.
 - simpl. unfold PortIndexFor8Ranks__portIndex8__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PortIndexFor8Ranks__portIndex8__Format : T_Format PortIndexFor8Ranks__portIndex8__Type PortIndexFor8Ranks__portIndex8__cond :=
        proj2_format  PortIndexFor8Ranks__portIndex8__cond PortIndexFor8Ranks__portIndex8__list__Format
    PortIndexFor8Ranks__portIndex8__F1 PortIndexFor8Ranks__portIndex8__F2 PortIndexFor8Ranks__portIndex8__F1F2_cond  PortIndexFor8Ranks__portIndex8__F1F2_cond2 PortIndexFor8Ranks__portIndex8__F2F1_cond.
Opaque PortIndexFor8Ranks__portIndex8__cond PortIndexFor8Ranks__portIndex8__Format.

Definition PortIndexFor8Ranks__portIndex4__rank2_4__Format : T_Format PortIndexFor8Ranks__portIndex4__rank2_4__Type PortIndexFor8Ranks__portIndex4__rank2_4__cond := seq_of_fixed_format PortIndex4__Format 2.

Opaque PortIndexFor8Ranks__portIndex4__rank2_4__cond PortIndexFor8Ranks__portIndex4__rank2_4__Format.

Definition PortIndexFor8Ranks__portIndex4__rank3_4__Format : T_Format PortIndexFor8Ranks__portIndex4__rank3_4__Type PortIndexFor8Ranks__portIndex4__rank3_4__cond := seq_of_fixed_format PortIndex4__Format 3.

Opaque PortIndexFor8Ranks__portIndex4__rank3_4__cond PortIndexFor8Ranks__portIndex4__rank3_4__Format.

Definition PortIndexFor8Ranks__portIndex4__rank4_4__Format : T_Format PortIndexFor8Ranks__portIndex4__rank4_4__Type PortIndexFor8Ranks__portIndex4__rank4_4__cond := seq_of_fixed_format PortIndex4__Format 4.

Opaque PortIndexFor8Ranks__portIndex4__rank4_4__cond PortIndexFor8Ranks__portIndex4__rank4_4__Format.


Definition PortIndexFor8Ranks__portIndex4__Format_Type := Eval cbn in seq_format_prod PortIndexFor8Ranks__portIndex4__list.
Definition PortIndexFor8Ranks__portIndex4__Format_list : PortIndexFor8Ranks__portIndex4__Format_Type :=
  (PortIndex4__Format, (PortIndexFor8Ranks__portIndex4__rank2_4__Format, (PortIndexFor8Ranks__portIndex4__rank3_4__Format, (PortIndexFor8Ranks__portIndex4__rank4_4__Format, unit_format)))).
Definition PortIndexFor8Ranks__portIndex4__list__Format := (*Eval compute in *) seq_format PortIndexFor8Ranks__portIndex4__list PortIndexFor8Ranks__portIndex4__Format_list.
Definition PortIndexFor8Ranks__portIndex4__F1 z :=
  (PortIndexFor8Ranks__portIndex4__rank1_4 z, (PortIndexFor8Ranks__portIndex4__rank2_4 z, (PortIndexFor8Ranks__portIndex4__rank3_4 z, (PortIndexFor8Ranks__portIndex4__rank4_4 z, tt)))).
Definition PortIndexFor8Ranks__portIndex4__F2 (y : seq_type PortIndexFor8Ranks__portIndex4__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PortIndexFor8Ranks__portIndex4__Type i0 i1 i2 i3
  end.
Lemma PortIndexFor8Ranks__portIndex4__F1F2_cond (z : PortIndexFor8Ranks__portIndex4__Type)
  : PortIndexFor8Ranks__portIndex4__cond z ->
  (seq_cond PortIndexFor8Ranks__portIndex4__list (PortIndexFor8Ranks__portIndex4__F1 z)).
intro H. unfold PortIndexFor8Ranks__portIndex4__cond in H. simpl. auto. Qed.
Lemma PortIndexFor8Ranks__portIndex4__F1F2_cond2 (z : PortIndexFor8Ranks__portIndex4__Type)
 : PortIndexFor8Ranks__portIndex4__F2 (PortIndexFor8Ranks__portIndex4__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PortIndexFor8Ranks__portIndex4__F2F1_cond (y : seq_type PortIndexFor8Ranks__portIndex4__list)
  : seq_cond PortIndexFor8Ranks__portIndex4__list y ->
 (PortIndexFor8Ranks__portIndex4__cond (PortIndexFor8Ranks__portIndex4__F2 y)) /\  PortIndexFor8Ranks__portIndex4__F1 (PortIndexFor8Ranks__portIndex4__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PortIndexFor8Ranks__portIndex4__cond. simpl in *. auto.
 - simpl. unfold PortIndexFor8Ranks__portIndex4__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PortIndexFor8Ranks__portIndex4__Format : T_Format PortIndexFor8Ranks__portIndex4__Type PortIndexFor8Ranks__portIndex4__cond :=
        proj2_format  PortIndexFor8Ranks__portIndex4__cond PortIndexFor8Ranks__portIndex4__list__Format
    PortIndexFor8Ranks__portIndex4__F1 PortIndexFor8Ranks__portIndex4__F2 PortIndexFor8Ranks__portIndex4__F1F2_cond  PortIndexFor8Ranks__portIndex4__F1F2_cond2 PortIndexFor8Ranks__portIndex4__F2F1_cond.
Opaque PortIndexFor8Ranks__portIndex4__cond PortIndexFor8Ranks__portIndex4__Format.

Definition PortIndexFor8Ranks__portIndex2__rank2_2__Format : T_Format PortIndexFor8Ranks__portIndex2__rank2_2__Type PortIndexFor8Ranks__portIndex2__rank2_2__cond := seq_of_fixed_format PortIndex2__Format 2.

Opaque PortIndexFor8Ranks__portIndex2__rank2_2__cond PortIndexFor8Ranks__portIndex2__rank2_2__Format.


Definition PortIndexFor8Ranks__portIndex2__Format_Type := Eval cbn in seq_format_prod PortIndexFor8Ranks__portIndex2__list.
Definition PortIndexFor8Ranks__portIndex2__Format_list : PortIndexFor8Ranks__portIndex2__Format_Type :=
  (PortIndex2__Format, (PortIndexFor8Ranks__portIndex2__rank2_2__Format, unit_format)).
Definition PortIndexFor8Ranks__portIndex2__list__Format := (*Eval compute in *) seq_format PortIndexFor8Ranks__portIndex2__list PortIndexFor8Ranks__portIndex2__Format_list.
Definition PortIndexFor8Ranks__portIndex2__F1 z :=
  (PortIndexFor8Ranks__portIndex2__rank1_2 z, (PortIndexFor8Ranks__portIndex2__rank2_2 z, tt)).
Definition PortIndexFor8Ranks__portIndex2__F2 (y : seq_type PortIndexFor8Ranks__portIndex2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PortIndexFor8Ranks__portIndex2__Type i0 i1
  end.
Lemma PortIndexFor8Ranks__portIndex2__F1F2_cond (z : PortIndexFor8Ranks__portIndex2__Type)
  : PortIndexFor8Ranks__portIndex2__cond z ->
  (seq_cond PortIndexFor8Ranks__portIndex2__list (PortIndexFor8Ranks__portIndex2__F1 z)).
intro H. unfold PortIndexFor8Ranks__portIndex2__cond in H. simpl. auto. Qed.
Lemma PortIndexFor8Ranks__portIndex2__F1F2_cond2 (z : PortIndexFor8Ranks__portIndex2__Type)
 : PortIndexFor8Ranks__portIndex2__F2 (PortIndexFor8Ranks__portIndex2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PortIndexFor8Ranks__portIndex2__F2F1_cond (y : seq_type PortIndexFor8Ranks__portIndex2__list)
  : seq_cond PortIndexFor8Ranks__portIndex2__list y ->
 (PortIndexFor8Ranks__portIndex2__cond (PortIndexFor8Ranks__portIndex2__F2 y)) /\  PortIndexFor8Ranks__portIndex2__F1 (PortIndexFor8Ranks__portIndex2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PortIndexFor8Ranks__portIndex2__cond. simpl in *. auto.
 - simpl. unfold PortIndexFor8Ranks__portIndex2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PortIndexFor8Ranks__portIndex2__Format : T_Format PortIndexFor8Ranks__portIndex2__Type PortIndexFor8Ranks__portIndex2__cond :=
        proj2_format  PortIndexFor8Ranks__portIndex2__cond PortIndexFor8Ranks__portIndex2__list__Format
    PortIndexFor8Ranks__portIndex2__F1 PortIndexFor8Ranks__portIndex2__F2 PortIndexFor8Ranks__portIndex2__F1F2_cond  PortIndexFor8Ranks__portIndex2__F1F2_cond2 PortIndexFor8Ranks__portIndex2__F2F1_cond.
Opaque PortIndexFor8Ranks__portIndex2__cond PortIndexFor8Ranks__portIndex2__Format.


Definition PortIndexFor8Ranks__Format_Type := Eval cbn in get_formats PortIndexFor8Ranks__list.
Definition PortIndexFor8Ranks__Format_list : PortIndexFor8Ranks__Format_Type :=
  (PortIndexFor8Ranks__portIndex8__Format, (PortIndexFor8Ranks__portIndex4__Format, (PortIndexFor8Ranks__portIndex2__Format, (unit__Format, unit__Format)))).
Definition PortIndexFor8Ranks__list__Format := Eval compute in choice_format PortIndexFor8Ranks__list PortIndexFor8Ranks__len_helper1 PortIndexFor8Ranks__len_helper2  PortIndexFor8Ranks__Format_list.
Definition PortIndexFor8Ranks__F1 (z : PortIndexFor8Ranks__Type) : (choice PortIndexFor8Ranks__list) :=
  match z with
   | PortIndexFor8Ranks__portIndex8 t => existT _ 0 t
  | PortIndexFor8Ranks__portIndex4 t => existT _ 1 t
  | PortIndexFor8Ranks__portIndex2 t => existT _ 2 t
  | PortIndexFor8Ranks__portIndex1 t => existT _ 3 t
  end.
Definition PortIndexFor8Ranks__g := (fun n => typ_set (get_nth_typ PortIndexFor8Ranks__list n)).
Definition PortIndexFor8Ranks__F2 (y : choice PortIndexFor8Ranks__list) : PortIndexFor8Ranks__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PortIndexFor8Ranks__g n -> PortIndexFor8Ranks__Type) with
    | 0 => fun (t : PortIndexFor8Ranks__portIndex8__Type) => PortIndexFor8Ranks__portIndex8 t 
    | 1 => fun (t : PortIndexFor8Ranks__portIndex4__Type) => PortIndexFor8Ranks__portIndex4 t 
    | 2 => fun (t : PortIndexFor8Ranks__portIndex2__Type) => PortIndexFor8Ranks__portIndex2 t 
    | 3 => fun (t : unit) => PortIndexFor8Ranks__portIndex1 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : PortIndexFor8Ranks__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ PortIndexFor8Ranks__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PortIndexFor8Ranks__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return PortIndexFor8Ranks__Type with end) n0
           end t0).

Lemma PortIndexFor8Ranks__helper2 :  forall (y : PortIndexFor8Ranks__Type), PortIndexFor8Ranks__cond y -> choice_cond PortIndexFor8Ranks__list (PortIndexFor8Ranks__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PortIndexFor8Ranks__helper3 :  forall (y : PortIndexFor8Ranks__Type), PortIndexFor8Ranks__F2 (PortIndexFor8Ranks__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PortIndexFor8Ranks__helper4 : (forall b : choice PortIndexFor8Ranks__list, choice_cond PortIndexFor8Ranks__list b -> PortIndexFor8Ranks__cond (PortIndexFor8Ranks__F2 b) /\ PortIndexFor8Ranks__F1 (PortIndexFor8Ranks__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PortIndexFor8Ranks__F1 PortIndexFor8Ranks__F2.
Definition PortIndexFor8Ranks__Format : T_Format PortIndexFor8Ranks__Type PortIndexFor8Ranks__cond :=
  (* Eval compute in *) proj2_format PortIndexFor8Ranks__cond PortIndexFor8Ranks__list__Format PortIndexFor8Ranks__F1 PortIndexFor8Ranks__F2 PortIndexFor8Ranks__helper2 PortIndexFor8Ranks__helper3 PortIndexFor8Ranks__helper4.
Opaque PortIndexFor8Ranks__cond PortIndexFor8Ranks__Format.

