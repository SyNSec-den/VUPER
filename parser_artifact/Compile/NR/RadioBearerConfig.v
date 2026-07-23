Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRB_ToAddModList.

Opaque SRB_ToAddModList__cond SRB_ToAddModList__Format.

Inductive RadioBearerConfig__srb3_ToRelease__Type : Set :=
 | RadioBearerConfig__srb3_ToRelease__true
.
Definition RadioBearerConfig__srb3_ToRelease__cond := (fun (_ : RadioBearerConfig__srb3_ToRelease__Type) => True).
Lemma RadioBearerConfig__srb3_ToRelease__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RadioBearerConfig__srb3_ToRelease__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RadioBearerConfig__srb3_ToRelease__nat__helper.

Definition RadioBearerConfig__srb3_ToRelease__F1 t :=
  match t with
  | RadioBearerConfig__srb3_ToRelease__true => 0
  end.
Definition RadioBearerConfig__srb3_ToRelease__F2 n :=
  match n with
  | 0 => RadioBearerConfig__srb3_ToRelease__true
  | _ => RadioBearerConfig__srb3_ToRelease__true
  end.
Lemma RadioBearerConfig__srb3_ToRelease__F1F2 : forall x : RadioBearerConfig__srb3_ToRelease__Type, (RadioBearerConfig__srb3_ToRelease__F1 x <= 0) /\ RadioBearerConfig__srb3_ToRelease__F2 (RadioBearerConfig__srb3_ToRelease__F1 x) = x. imp_solve. Qed.
Lemma RadioBearerConfig__srb3_ToRelease__F2F1 : forall (y : nat) (H : y <= 0), RadioBearerConfig__srb3_ToRelease__F1 (RadioBearerConfig__srb3_ToRelease__F2 y) = y. enum_solve H y. Qed.

Require Import NR.DRB_ToAddModList.

Opaque DRB_ToAddModList__cond DRB_ToAddModList__Format.

Require Import NR.DRB_ToReleaseList.

Opaque DRB_ToReleaseList__cond DRB_ToReleaseList__Format.

Require Import NR.SecurityConfig.

Opaque SecurityConfig__cond SecurityConfig__Format.

Require Import NR.MRB_ToAddModList_r17.

Opaque MRB_ToAddModList_r17__cond MRB_ToAddModList_r17__Format.

Require Import NR.MRB_ToReleaseList_r17.

Opaque MRB_ToReleaseList_r17__cond MRB_ToReleaseList_r17__Format.

Require Import NR.SRB_ToAddMod.

Opaque SRB_ToAddMod__cond SRB_ToAddMod__Format.

Inductive RadioBearerConfig__ext0O__srb4_ToRelease_r17__Type : Set :=
 | RadioBearerConfig__ext0O__srb4_ToRelease_r17__true
.
Definition RadioBearerConfig__ext0O__srb4_ToRelease_r17__cond := (fun (_ : RadioBearerConfig__ext0O__srb4_ToRelease_r17__Type) => True).
Lemma RadioBearerConfig__ext0O__srb4_ToRelease_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RadioBearerConfig__ext0O__srb4_ToRelease_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RadioBearerConfig__ext0O__srb4_ToRelease_r17__nat__helper.

Definition RadioBearerConfig__ext0O__srb4_ToRelease_r17__F1 t :=
  match t with
  | RadioBearerConfig__ext0O__srb4_ToRelease_r17__true => 0
  end.
Definition RadioBearerConfig__ext0O__srb4_ToRelease_r17__F2 n :=
  match n with
  | 0 => RadioBearerConfig__ext0O__srb4_ToRelease_r17__true
  | _ => RadioBearerConfig__ext0O__srb4_ToRelease_r17__true
  end.
Lemma RadioBearerConfig__ext0O__srb4_ToRelease_r17__F1F2 : forall x : RadioBearerConfig__ext0O__srb4_ToRelease_r17__Type, (RadioBearerConfig__ext0O__srb4_ToRelease_r17__F1 x <= 0) /\ RadioBearerConfig__ext0O__srb4_ToRelease_r17__F2 (RadioBearerConfig__ext0O__srb4_ToRelease_r17__F1 x) = x. imp_solve. Qed.
Lemma RadioBearerConfig__ext0O__srb4_ToRelease_r17__F2F1 : forall (y : nat) (H : y <= 0), RadioBearerConfig__ext0O__srb4_ToRelease_r17__F1 (RadioBearerConfig__ext0O__srb4_ToRelease_r17__F2 y) = y. enum_solve H y. Qed.

Record RadioBearerConfig__ext0O__Type : Set :=
  make__RadioBearerConfig__ext0O__Type {
    RadioBearerConfig__ext0O__mrb_ToAddModList_r17 : option MRB_ToAddModList_r17__Type ;
    RadioBearerConfig__ext0O__mrb_ToReleaseList_r17 : option MRB_ToReleaseList_r17__Type ;
    RadioBearerConfig__ext0O__srb4_ToAddMod_r17 : option SRB_ToAddMod__Type ;
    RadioBearerConfig__ext0O__srb4_ToRelease_r17 : option RadioBearerConfig__ext0O__srb4_ToRelease_r17__Type ;
}.
Definition RadioBearerConfig__ext0O__list := (
 Opt MRB_ToAddModList_r17__Type MRB_ToAddModList_r17__cond ::
 Opt MRB_ToReleaseList_r17__Type MRB_ToReleaseList_r17__cond ::
 Opt SRB_ToAddMod__Type SRB_ToAddMod__cond ::
 Opt RadioBearerConfig__ext0O__srb4_ToRelease_r17__Type RadioBearerConfig__ext0O__srb4_ToRelease_r17__cond ::
 nil).
Definition RadioBearerConfig__ext0O__cond z := 
  opt_cond MRB_ToAddModList_r17__cond (RadioBearerConfig__ext0O__mrb_ToAddModList_r17 z) /\
  opt_cond MRB_ToReleaseList_r17__cond (RadioBearerConfig__ext0O__mrb_ToReleaseList_r17 z) /\
  opt_cond SRB_ToAddMod__cond (RadioBearerConfig__ext0O__srb4_ToAddMod_r17 z) /\
  opt_cond RadioBearerConfig__ext0O__srb4_ToRelease_r17__cond (RadioBearerConfig__ext0O__srb4_ToRelease_r17 z) /\
  True.

Definition RadioBearerConfig__ext0__Type := RadioBearerConfig__ext0O__Type.
Definition RadioBearerConfig__ext0__cond := RadioBearerConfig__ext0O__cond.

Record RadioBearerConfig__Type : Set :=
  make__RadioBearerConfig__Type {
    RadioBearerConfig__srb_ToAddModList : option SRB_ToAddModList__Type ;
    RadioBearerConfig__srb3_ToRelease : option RadioBearerConfig__srb3_ToRelease__Type ;
    RadioBearerConfig__drb_ToAddModList : option DRB_ToAddModList__Type ;
    RadioBearerConfig__drb_ToReleaseList : option DRB_ToReleaseList__Type ;
    RadioBearerConfig__securityConfig : option SecurityConfig__Type ;
    RadioBearerConfig__ext0 : option RadioBearerConfig__ext0__Type ;
}.
Definition RadioBearerConfig__root_list : list seq_elem := (
 Opt SRB_ToAddModList__Type SRB_ToAddModList__cond ::
 Opt RadioBearerConfig__srb3_ToRelease__Type RadioBearerConfig__srb3_ToRelease__cond ::
 Opt DRB_ToAddModList__Type DRB_ToAddModList__cond ::
 Opt DRB_ToReleaseList__Type DRB_ToReleaseList__cond ::
 Opt SecurityConfig__Type SecurityConfig__cond ::
 nil).
Definition RadioBearerConfig__ext_list : list typ := (
  typ_cons RadioBearerConfig__ext0__Type RadioBearerConfig__ext0__cond ::
  nil).
Definition RadioBearerConfig__cond (z : RadioBearerConfig__Type) := 
(  opt_cond SRB_ToAddModList__cond (RadioBearerConfig__srb_ToAddModList z) /\
  opt_cond RadioBearerConfig__srb3_ToRelease__cond (RadioBearerConfig__srb3_ToRelease z) /\
  opt_cond DRB_ToAddModList__cond (RadioBearerConfig__drb_ToAddModList z) /\
  opt_cond DRB_ToReleaseList__cond (RadioBearerConfig__drb_ToReleaseList z) /\
  opt_cond SecurityConfig__cond (RadioBearerConfig__securityConfig z) /\
  True) /\ 
(  opt_cond RadioBearerConfig__ext0__cond (RadioBearerConfig__ext0 z) /\
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
Definition RadioBearerConfig__srb3_ToRelease__Format : T_Format RadioBearerConfig__srb3_ToRelease__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RadioBearerConfig__srb3_ToRelease__nat__Format RadioBearerConfig__srb3_ToRelease__F1 RadioBearerConfig__srb3_ToRelease__F2 RadioBearerConfig__srb3_ToRelease__F1F2 RadioBearerConfig__srb3_ToRelease__F2F1.

Opaque RadioBearerConfig__srb3_ToRelease__cond RadioBearerConfig__srb3_ToRelease__Format.

Definition RadioBearerConfig__ext0O__srb4_ToRelease_r17__Format : T_Format RadioBearerConfig__ext0O__srb4_ToRelease_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RadioBearerConfig__ext0O__srb4_ToRelease_r17__nat__Format RadioBearerConfig__ext0O__srb4_ToRelease_r17__F1 RadioBearerConfig__ext0O__srb4_ToRelease_r17__F2 RadioBearerConfig__ext0O__srb4_ToRelease_r17__F1F2 RadioBearerConfig__ext0O__srb4_ToRelease_r17__F2F1.

Opaque RadioBearerConfig__ext0O__srb4_ToRelease_r17__cond RadioBearerConfig__ext0O__srb4_ToRelease_r17__Format.


Definition RadioBearerConfig__ext0O__Format_Type := Eval cbn in seq_format_prod RadioBearerConfig__ext0O__list.
Definition RadioBearerConfig__ext0O__Format_list : RadioBearerConfig__ext0O__Format_Type :=
  (MRB_ToAddModList_r17__Format, (MRB_ToReleaseList_r17__Format, (SRB_ToAddMod__Format, (RadioBearerConfig__ext0O__srb4_ToRelease_r17__Format, unit_format)))).
Definition RadioBearerConfig__ext0O__list__Format := (*Eval compute in *) seq_format RadioBearerConfig__ext0O__list RadioBearerConfig__ext0O__Format_list.
Definition RadioBearerConfig__ext0O__F1 z :=
  (RadioBearerConfig__ext0O__mrb_ToAddModList_r17 z, (RadioBearerConfig__ext0O__mrb_ToReleaseList_r17 z, (RadioBearerConfig__ext0O__srb4_ToAddMod_r17 z, (RadioBearerConfig__ext0O__srb4_ToRelease_r17 z, tt)))).
Definition RadioBearerConfig__ext0O__F2 (y : seq_type RadioBearerConfig__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__RadioBearerConfig__ext0O__Type i0 i1 i2 i3
  end.
Lemma RadioBearerConfig__ext0O__F1F2_cond (z : RadioBearerConfig__ext0O__Type)
  : RadioBearerConfig__ext0O__cond z ->
  (seq_cond RadioBearerConfig__ext0O__list (RadioBearerConfig__ext0O__F1 z)).
intro H. unfold RadioBearerConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma RadioBearerConfig__ext0O__F1F2_cond2 (z : RadioBearerConfig__ext0O__Type)
 : RadioBearerConfig__ext0O__F2 (RadioBearerConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RadioBearerConfig__ext0O__F2F1_cond (y : seq_type RadioBearerConfig__ext0O__list)
  : seq_cond RadioBearerConfig__ext0O__list y ->
 (RadioBearerConfig__ext0O__cond (RadioBearerConfig__ext0O__F2 y)) /\  RadioBearerConfig__ext0O__F1 (RadioBearerConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RadioBearerConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold RadioBearerConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RadioBearerConfig__ext0O__Format : T_Format RadioBearerConfig__ext0O__Type RadioBearerConfig__ext0O__cond :=
        proj2_format  RadioBearerConfig__ext0O__cond RadioBearerConfig__ext0O__list__Format
    RadioBearerConfig__ext0O__F1 RadioBearerConfig__ext0O__F2 RadioBearerConfig__ext0O__F1F2_cond  RadioBearerConfig__ext0O__F1F2_cond2 RadioBearerConfig__ext0O__F2F1_cond.
Opaque RadioBearerConfig__ext0O__cond RadioBearerConfig__ext0O__Format.

Definition RadioBearerConfig__ext0__check_all_none (b : RadioBearerConfig__ext0O__Type) : bool :=
match b with 
  | make__RadioBearerConfig__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition RadioBearerConfig__ext0__Format : T_Format RadioBearerConfig__ext0__Type RadioBearerConfig__ext0__cond :=
  restrict_add_format RadioBearerConfig__ext0__check_all_none RadioBearerConfig__ext0O__Format.

Opaque RadioBearerConfig__ext0__cond RadioBearerConfig__ext0__Format.


Definition RadioBearerConfig__root_Format_Type := Eval cbn in seq_format_prod RadioBearerConfig__root_list.
Definition RadioBearerConfig__root_Format_list : RadioBearerConfig__root_Format_Type :=
  (SRB_ToAddModList__Format, (RadioBearerConfig__srb3_ToRelease__Format, (DRB_ToAddModList__Format, (DRB_ToReleaseList__Format, (SecurityConfig__Format, unit_format))))).

Definition RadioBearerConfig__ext_Format_Type := Eval cbn in get_formats RadioBearerConfig__ext_list.
Definition RadioBearerConfig__ext_Format_list : RadioBearerConfig__ext_Format_Type :=
  (RadioBearerConfig__ext0__Format, unit__Format).

Definition RadioBearerConfig__list_type : Set := (seq_type RadioBearerConfig__root_list) * (seq_ext_type RadioBearerConfig__ext_list).
Definition RadioBearerConfig__list_cond (z : RadioBearerConfig__list_type) : Prop :=
        (seq_cond RadioBearerConfig__root_list (fst z)) /\ (seq_ext_cond RadioBearerConfig__ext_list (snd z)).
Definition RadioBearerConfig__list_format : T_Format RadioBearerConfig__list_type RadioBearerConfig__list_cond :=
 (* Eval compute in *) seq_ext_format RadioBearerConfig__root_list RadioBearerConfig__root_Format_list RadioBearerConfig__ext_list RadioBearerConfig__ext_Format_list.

Opaque RadioBearerConfig__list_format.
Definition RadioBearerConfig__F1 (z : RadioBearerConfig__Type) : RadioBearerConfig__list_type :=
  (((RadioBearerConfig__srb_ToAddModList z, (RadioBearerConfig__srb3_ToRelease z, (RadioBearerConfig__drb_ToAddModList z, (RadioBearerConfig__drb_ToReleaseList z, (RadioBearerConfig__securityConfig z, tt)))))), (
(RadioBearerConfig__ext0 z, tt))).
Definition RadioBearerConfig__F2 (y : RadioBearerConfig__list_type) : RadioBearerConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, _))=>
    make__RadioBearerConfig__Type j0 j1 j2 j3 j4 i0
  end.
Definition RadioBearerConfig__helper1 : (forall a : RadioBearerConfig__Type, RadioBearerConfig__cond a -> RadioBearerConfig__list_cond (RadioBearerConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RadioBearerConfig__helper2 : (forall a : RadioBearerConfig__Type, RadioBearerConfig__F2 (RadioBearerConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RadioBearerConfig__helper3 : (forall b : RadioBearerConfig__list_type, RadioBearerConfig__list_cond b -> RadioBearerConfig__cond (RadioBearerConfig__F2 b) /\ RadioBearerConfig__F1 (RadioBearerConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RadioBearerConfig__cond, RadioBearerConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RadioBearerConfig__Format : T_Format RadioBearerConfig__Type RadioBearerConfig__cond :=
 proj2_format RadioBearerConfig__cond RadioBearerConfig__list_format  RadioBearerConfig__F1 RadioBearerConfig__F2 RadioBearerConfig__helper1 RadioBearerConfig__helper2 RadioBearerConfig__helper3.

Opaque RadioBearerConfig__cond RadioBearerConfig__Format.

