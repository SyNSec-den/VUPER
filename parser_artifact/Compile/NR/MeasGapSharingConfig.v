Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.MeasGapSharingScheme.
Definition MeasGapSharingConfig__gapSharingFR2__Type := SetupRelease__Type MeasGapSharingScheme__Type.
Definition MeasGapSharingConfig__gapSharingFR2__cond := SetupRelease__cond _ MeasGapSharingScheme__cond.
Definition MeasGapSharingConfig__gapSharingFR2__Format : T_Format MeasGapSharingConfig__gapSharingFR2__Type MeasGapSharingConfig__gapSharingFR2__cond := SetupRelease__Format _ _ MeasGapSharingScheme__Format.
Opaque MeasGapSharingConfig__gapSharingFR2__cond MeasGapSharingConfig__gapSharingFR2__Format.

Require Import NR.SetupRelease.
Require Import NR.MeasGapSharingScheme.
Definition MeasGapSharingConfig__ext0O__gapSharingFR1__Type := SetupRelease__Type MeasGapSharingScheme__Type.
Definition MeasGapSharingConfig__ext0O__gapSharingFR1__cond := SetupRelease__cond _ MeasGapSharingScheme__cond.
Definition MeasGapSharingConfig__ext0O__gapSharingFR1__Format : T_Format MeasGapSharingConfig__ext0O__gapSharingFR1__Type MeasGapSharingConfig__ext0O__gapSharingFR1__cond := SetupRelease__Format _ _ MeasGapSharingScheme__Format.
Opaque MeasGapSharingConfig__ext0O__gapSharingFR1__cond MeasGapSharingConfig__ext0O__gapSharingFR1__Format.

Require Import NR.SetupRelease.
Require Import NR.MeasGapSharingScheme.
Definition MeasGapSharingConfig__ext0O__gapSharingUE__Type := SetupRelease__Type MeasGapSharingScheme__Type.
Definition MeasGapSharingConfig__ext0O__gapSharingUE__cond := SetupRelease__cond _ MeasGapSharingScheme__cond.
Definition MeasGapSharingConfig__ext0O__gapSharingUE__Format : T_Format MeasGapSharingConfig__ext0O__gapSharingUE__Type MeasGapSharingConfig__ext0O__gapSharingUE__cond := SetupRelease__Format _ _ MeasGapSharingScheme__Format.
Opaque MeasGapSharingConfig__ext0O__gapSharingUE__cond MeasGapSharingConfig__ext0O__gapSharingUE__Format.

Record MeasGapSharingConfig__ext0O__Type : Set :=
  make__MeasGapSharingConfig__ext0O__Type {
    MeasGapSharingConfig__ext0O__gapSharingFR1 : option MeasGapSharingConfig__ext0O__gapSharingFR1__Type ;
    MeasGapSharingConfig__ext0O__gapSharingUE : option MeasGapSharingConfig__ext0O__gapSharingUE__Type ;
}.
Definition MeasGapSharingConfig__ext0O__list := (
 Opt MeasGapSharingConfig__ext0O__gapSharingFR1__Type MeasGapSharingConfig__ext0O__gapSharingFR1__cond ::
 Opt MeasGapSharingConfig__ext0O__gapSharingUE__Type MeasGapSharingConfig__ext0O__gapSharingUE__cond ::
 nil).
Definition MeasGapSharingConfig__ext0O__cond z := 
  opt_cond MeasGapSharingConfig__ext0O__gapSharingFR1__cond (MeasGapSharingConfig__ext0O__gapSharingFR1 z) /\
  opt_cond MeasGapSharingConfig__ext0O__gapSharingUE__cond (MeasGapSharingConfig__ext0O__gapSharingUE z) /\
  True.

Definition MeasGapSharingConfig__ext0__Type := MeasGapSharingConfig__ext0O__Type.
Definition MeasGapSharingConfig__ext0__cond := MeasGapSharingConfig__ext0O__cond.

Record MeasGapSharingConfig__Type : Set :=
  make__MeasGapSharingConfig__Type {
    MeasGapSharingConfig__gapSharingFR2 : option MeasGapSharingConfig__gapSharingFR2__Type ;
    MeasGapSharingConfig__ext0 : option MeasGapSharingConfig__ext0__Type ;
}.
Definition MeasGapSharingConfig__root_list : list seq_elem := (
 Opt MeasGapSharingConfig__gapSharingFR2__Type MeasGapSharingConfig__gapSharingFR2__cond ::
 nil).
Definition MeasGapSharingConfig__ext_list : list typ := (
  typ_cons MeasGapSharingConfig__ext0__Type MeasGapSharingConfig__ext0__cond ::
  nil).
Definition MeasGapSharingConfig__cond (z : MeasGapSharingConfig__Type) := 
(  opt_cond MeasGapSharingConfig__gapSharingFR2__cond (MeasGapSharingConfig__gapSharingFR2 z) /\
  True) /\ 
(  opt_cond MeasGapSharingConfig__ext0__cond (MeasGapSharingConfig__ext0 z) /\
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
Opaque MeasGapSharingConfig__gapSharingFR2__cond MeasGapSharingConfig__gapSharingFR2__Format.

Opaque MeasGapSharingConfig__ext0O__gapSharingFR1__cond MeasGapSharingConfig__ext0O__gapSharingFR1__Format.

Opaque MeasGapSharingConfig__ext0O__gapSharingUE__cond MeasGapSharingConfig__ext0O__gapSharingUE__Format.


Definition MeasGapSharingConfig__ext0O__Format_Type := Eval cbn in seq_format_prod MeasGapSharingConfig__ext0O__list.
Definition MeasGapSharingConfig__ext0O__Format_list : MeasGapSharingConfig__ext0O__Format_Type :=
  (MeasGapSharingConfig__ext0O__gapSharingFR1__Format, (MeasGapSharingConfig__ext0O__gapSharingUE__Format, unit_format)).
Definition MeasGapSharingConfig__ext0O__list__Format := (*Eval compute in *) seq_format MeasGapSharingConfig__ext0O__list MeasGapSharingConfig__ext0O__Format_list.
Definition MeasGapSharingConfig__ext0O__F1 z :=
  (MeasGapSharingConfig__ext0O__gapSharingFR1 z, (MeasGapSharingConfig__ext0O__gapSharingUE z, tt)).
Definition MeasGapSharingConfig__ext0O__F2 (y : seq_type MeasGapSharingConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasGapSharingConfig__ext0O__Type i0 i1
  end.
Lemma MeasGapSharingConfig__ext0O__F1F2_cond (z : MeasGapSharingConfig__ext0O__Type)
  : MeasGapSharingConfig__ext0O__cond z ->
  (seq_cond MeasGapSharingConfig__ext0O__list (MeasGapSharingConfig__ext0O__F1 z)).
intro H. unfold MeasGapSharingConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasGapSharingConfig__ext0O__F1F2_cond2 (z : MeasGapSharingConfig__ext0O__Type)
 : MeasGapSharingConfig__ext0O__F2 (MeasGapSharingConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasGapSharingConfig__ext0O__F2F1_cond (y : seq_type MeasGapSharingConfig__ext0O__list)
  : seq_cond MeasGapSharingConfig__ext0O__list y ->
 (MeasGapSharingConfig__ext0O__cond (MeasGapSharingConfig__ext0O__F2 y)) /\  MeasGapSharingConfig__ext0O__F1 (MeasGapSharingConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasGapSharingConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasGapSharingConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasGapSharingConfig__ext0O__Format : T_Format MeasGapSharingConfig__ext0O__Type MeasGapSharingConfig__ext0O__cond :=
        proj2_format  MeasGapSharingConfig__ext0O__cond MeasGapSharingConfig__ext0O__list__Format
    MeasGapSharingConfig__ext0O__F1 MeasGapSharingConfig__ext0O__F2 MeasGapSharingConfig__ext0O__F1F2_cond  MeasGapSharingConfig__ext0O__F1F2_cond2 MeasGapSharingConfig__ext0O__F2F1_cond.
Opaque MeasGapSharingConfig__ext0O__cond MeasGapSharingConfig__ext0O__Format.

Definition MeasGapSharingConfig__ext0__check_all_none (b : MeasGapSharingConfig__ext0O__Type) : bool :=
match b with 
  | make__MeasGapSharingConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition MeasGapSharingConfig__ext0__Format : T_Format MeasGapSharingConfig__ext0__Type MeasGapSharingConfig__ext0__cond :=
  restrict_add_format MeasGapSharingConfig__ext0__check_all_none MeasGapSharingConfig__ext0O__Format.

Opaque MeasGapSharingConfig__ext0__cond MeasGapSharingConfig__ext0__Format.


Definition MeasGapSharingConfig__root_Format_Type := Eval cbn in seq_format_prod MeasGapSharingConfig__root_list.
Definition MeasGapSharingConfig__root_Format_list : MeasGapSharingConfig__root_Format_Type :=
  (MeasGapSharingConfig__gapSharingFR2__Format, unit_format).

Definition MeasGapSharingConfig__ext_Format_Type := Eval cbn in get_formats MeasGapSharingConfig__ext_list.
Definition MeasGapSharingConfig__ext_Format_list : MeasGapSharingConfig__ext_Format_Type :=
  (MeasGapSharingConfig__ext0__Format, unit__Format).

Definition MeasGapSharingConfig__list_type : Set := (seq_type MeasGapSharingConfig__root_list) * (seq_ext_type MeasGapSharingConfig__ext_list).
Definition MeasGapSharingConfig__list_cond (z : MeasGapSharingConfig__list_type) : Prop :=
        (seq_cond MeasGapSharingConfig__root_list (fst z)) /\ (seq_ext_cond MeasGapSharingConfig__ext_list (snd z)).
Definition MeasGapSharingConfig__list_format : T_Format MeasGapSharingConfig__list_type MeasGapSharingConfig__list_cond :=
 (* Eval compute in *) seq_ext_format MeasGapSharingConfig__root_list MeasGapSharingConfig__root_Format_list MeasGapSharingConfig__ext_list MeasGapSharingConfig__ext_Format_list.

Opaque MeasGapSharingConfig__list_format.
Definition MeasGapSharingConfig__F1 (z : MeasGapSharingConfig__Type) : MeasGapSharingConfig__list_type :=
  (((MeasGapSharingConfig__gapSharingFR2 z, tt)), (
(MeasGapSharingConfig__ext0 z, tt))).
Definition MeasGapSharingConfig__F2 (y : MeasGapSharingConfig__list_type) : MeasGapSharingConfig__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__MeasGapSharingConfig__Type j0 i0
  end.
Definition MeasGapSharingConfig__helper1 : (forall a : MeasGapSharingConfig__Type, MeasGapSharingConfig__cond a -> MeasGapSharingConfig__list_cond (MeasGapSharingConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasGapSharingConfig__helper2 : (forall a : MeasGapSharingConfig__Type, MeasGapSharingConfig__F2 (MeasGapSharingConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasGapSharingConfig__helper3 : (forall b : MeasGapSharingConfig__list_type, MeasGapSharingConfig__list_cond b -> MeasGapSharingConfig__cond (MeasGapSharingConfig__F2 b) /\ MeasGapSharingConfig__F1 (MeasGapSharingConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasGapSharingConfig__cond, MeasGapSharingConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasGapSharingConfig__Format : T_Format MeasGapSharingConfig__Type MeasGapSharingConfig__cond :=
 proj2_format MeasGapSharingConfig__cond MeasGapSharingConfig__list_format  MeasGapSharingConfig__F1 MeasGapSharingConfig__F2 MeasGapSharingConfig__helper1 MeasGapSharingConfig__helper2 MeasGapSharingConfig__helper3.

Opaque MeasGapSharingConfig__cond MeasGapSharingConfig__Format.

