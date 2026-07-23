Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma GapConfig__gapOffset__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma GapConfig__gapOffset__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply GapConfig__gapOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition GapConfig__gapOffset__Type := Z.
Definition GapConfig__gapOffset__cond := (fun z => (0 <= z <= 159)%Z).
Inductive GapConfig__mgl__Type : Set :=
 | GapConfig__mgl__ms1dot5
 | GapConfig__mgl__ms3
 | GapConfig__mgl__ms3dot5
 | GapConfig__mgl__ms4
 | GapConfig__mgl__ms5dot5
 | GapConfig__mgl__ms6
.
Definition GapConfig__mgl__cond := (fun (_ : GapConfig__mgl__Type) => True).
Lemma GapConfig__mgl__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig__mgl__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 GapConfig__mgl__nat__helper.

Definition GapConfig__mgl__F1 t :=
  match t with
  | GapConfig__mgl__ms1dot5 => 0
  | GapConfig__mgl__ms3 => 1
  | GapConfig__mgl__ms3dot5 => 2
  | GapConfig__mgl__ms4 => 3
  | GapConfig__mgl__ms5dot5 => 4
  | GapConfig__mgl__ms6 => 5
  end.
Definition GapConfig__mgl__F2 n :=
  match n with
  | 0 => GapConfig__mgl__ms1dot5
  | 1 => GapConfig__mgl__ms3
  | 2 => GapConfig__mgl__ms3dot5
  | 3 => GapConfig__mgl__ms4
  | 4 => GapConfig__mgl__ms5dot5
  | 5 => GapConfig__mgl__ms6
  | _ => GapConfig__mgl__ms1dot5
  end.
Lemma GapConfig__mgl__F1F2 : forall x : GapConfig__mgl__Type, (GapConfig__mgl__F1 x <= 5) /\ GapConfig__mgl__F2 (GapConfig__mgl__F1 x) = x. imp_solve. Qed.
Lemma GapConfig__mgl__F2F1 : forall (y : nat) (H : y <= 5), GapConfig__mgl__F1 (GapConfig__mgl__F2 y) = y. enum_solve H y. Qed.

Inductive GapConfig__mgrp__Type : Set :=
 | GapConfig__mgrp__ms20
 | GapConfig__mgrp__ms40
 | GapConfig__mgrp__ms80
 | GapConfig__mgrp__ms160
.
Definition GapConfig__mgrp__cond := (fun (_ : GapConfig__mgrp__Type) => True).
Lemma GapConfig__mgrp__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig__mgrp__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 GapConfig__mgrp__nat__helper.

Definition GapConfig__mgrp__F1 t :=
  match t with
  | GapConfig__mgrp__ms20 => 0
  | GapConfig__mgrp__ms40 => 1
  | GapConfig__mgrp__ms80 => 2
  | GapConfig__mgrp__ms160 => 3
  end.
Definition GapConfig__mgrp__F2 n :=
  match n with
  | 0 => GapConfig__mgrp__ms20
  | 1 => GapConfig__mgrp__ms40
  | 2 => GapConfig__mgrp__ms80
  | 3 => GapConfig__mgrp__ms160
  | _ => GapConfig__mgrp__ms20
  end.
Lemma GapConfig__mgrp__F1F2 : forall x : GapConfig__mgrp__Type, (GapConfig__mgrp__F1 x <= 3) /\ GapConfig__mgrp__F2 (GapConfig__mgrp__F1 x) = x. imp_solve. Qed.
Lemma GapConfig__mgrp__F2F1 : forall (y : nat) (H : y <= 3), GapConfig__mgrp__F1 (GapConfig__mgrp__F2 y) = y. enum_solve H y. Qed.

Inductive GapConfig__mgta__Type : Set :=
 | GapConfig__mgta__ms0
 | GapConfig__mgta__ms0dot25
 | GapConfig__mgta__ms0dot5
.
Definition GapConfig__mgta__cond := (fun (_ : GapConfig__mgta__Type) => True).
Lemma GapConfig__mgta__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig__mgta__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 GapConfig__mgta__nat__helper.

Definition GapConfig__mgta__F1 t :=
  match t with
  | GapConfig__mgta__ms0 => 0
  | GapConfig__mgta__ms0dot25 => 1
  | GapConfig__mgta__ms0dot5 => 2
  end.
Definition GapConfig__mgta__F2 n :=
  match n with
  | 0 => GapConfig__mgta__ms0
  | 1 => GapConfig__mgta__ms0dot25
  | 2 => GapConfig__mgta__ms0dot5
  | _ => GapConfig__mgta__ms0
  end.
Lemma GapConfig__mgta__F1F2 : forall x : GapConfig__mgta__Type, (GapConfig__mgta__F1 x <= 2) /\ GapConfig__mgta__F2 (GapConfig__mgta__F1 x) = x. imp_solve. Qed.
Lemma GapConfig__mgta__F2F1 : forall (y : nat) (H : y <= 2), GapConfig__mgta__F1 (GapConfig__mgta__F2 y) = y. enum_solve H y. Qed.

Inductive GapConfig__ext0O__refServCellIndicator__Type : Set :=
 | GapConfig__ext0O__refServCellIndicator__pCell
 | GapConfig__ext0O__refServCellIndicator__pSCell
 | GapConfig__ext0O__refServCellIndicator__mcg_FR2
.
Definition GapConfig__ext0O__refServCellIndicator__cond := (fun (_ : GapConfig__ext0O__refServCellIndicator__Type) => True).
Lemma GapConfig__ext0O__refServCellIndicator__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig__ext0O__refServCellIndicator__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 GapConfig__ext0O__refServCellIndicator__nat__helper.

Definition GapConfig__ext0O__refServCellIndicator__F1 t :=
  match t with
  | GapConfig__ext0O__refServCellIndicator__pCell => 0
  | GapConfig__ext0O__refServCellIndicator__pSCell => 1
  | GapConfig__ext0O__refServCellIndicator__mcg_FR2 => 2
  end.
Definition GapConfig__ext0O__refServCellIndicator__F2 n :=
  match n with
  | 0 => GapConfig__ext0O__refServCellIndicator__pCell
  | 1 => GapConfig__ext0O__refServCellIndicator__pSCell
  | 2 => GapConfig__ext0O__refServCellIndicator__mcg_FR2
  | _ => GapConfig__ext0O__refServCellIndicator__pCell
  end.
Lemma GapConfig__ext0O__refServCellIndicator__F1F2 : forall x : GapConfig__ext0O__refServCellIndicator__Type, (GapConfig__ext0O__refServCellIndicator__F1 x <= 2) /\ GapConfig__ext0O__refServCellIndicator__F2 (GapConfig__ext0O__refServCellIndicator__F1 x) = x. imp_solve. Qed.
Lemma GapConfig__ext0O__refServCellIndicator__F2F1 : forall (y : nat) (H : y <= 2), GapConfig__ext0O__refServCellIndicator__F1 (GapConfig__ext0O__refServCellIndicator__F2 y) = y. enum_solve H y. Qed.

Record GapConfig__ext0O__Type : Set :=
  make__GapConfig__ext0O__Type {
    GapConfig__ext0O__refServCellIndicator : option GapConfig__ext0O__refServCellIndicator__Type ;
}.
Definition GapConfig__ext0O__list := (
 Opt GapConfig__ext0O__refServCellIndicator__Type GapConfig__ext0O__refServCellIndicator__cond ::
 nil).
Definition GapConfig__ext0O__cond z := 
  opt_cond GapConfig__ext0O__refServCellIndicator__cond (GapConfig__ext0O__refServCellIndicator z) /\
  True.

Definition GapConfig__ext0__Type := GapConfig__ext0O__Type.
Definition GapConfig__ext0__cond := GapConfig__ext0O__cond.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Inductive GapConfig__ext1O__mgl_r16__Type : Set :=
 | GapConfig__ext1O__mgl_r16__ms10
 | GapConfig__ext1O__mgl_r16__ms20
.
Definition GapConfig__ext1O__mgl_r16__cond := (fun (_ : GapConfig__ext1O__mgl_r16__Type) => True).
Lemma GapConfig__ext1O__mgl_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig__ext1O__mgl_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 GapConfig__ext1O__mgl_r16__nat__helper.

Definition GapConfig__ext1O__mgl_r16__F1 t :=
  match t with
  | GapConfig__ext1O__mgl_r16__ms10 => 0
  | GapConfig__ext1O__mgl_r16__ms20 => 1
  end.
Definition GapConfig__ext1O__mgl_r16__F2 n :=
  match n with
  | 0 => GapConfig__ext1O__mgl_r16__ms10
  | 1 => GapConfig__ext1O__mgl_r16__ms20
  | _ => GapConfig__ext1O__mgl_r16__ms10
  end.
Lemma GapConfig__ext1O__mgl_r16__F1F2 : forall x : GapConfig__ext1O__mgl_r16__Type, (GapConfig__ext1O__mgl_r16__F1 x <= 1) /\ GapConfig__ext1O__mgl_r16__F2 (GapConfig__ext1O__mgl_r16__F1 x) = x. imp_solve. Qed.
Lemma GapConfig__ext1O__mgl_r16__F2F1 : forall (y : nat) (H : y <= 1), GapConfig__ext1O__mgl_r16__F1 (GapConfig__ext1O__mgl_r16__F2 y) = y. enum_solve H y. Qed.

Record GapConfig__ext1O__Type : Set :=
  make__GapConfig__ext1O__Type {
    GapConfig__ext1O__refFR2ServCellAsyncCA_r16 : option ServCellIndex__Type ;
    GapConfig__ext1O__mgl_r16 : option GapConfig__ext1O__mgl_r16__Type ;
}.
Definition GapConfig__ext1O__list := (
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Opt GapConfig__ext1O__mgl_r16__Type GapConfig__ext1O__mgl_r16__cond ::
 nil).
Definition GapConfig__ext1O__cond z := 
  opt_cond ServCellIndex__cond (GapConfig__ext1O__refFR2ServCellAsyncCA_r16 z) /\
  opt_cond GapConfig__ext1O__mgl_r16__cond (GapConfig__ext1O__mgl_r16 z) /\
  True.

Definition GapConfig__ext1__Type := GapConfig__ext1O__Type.
Definition GapConfig__ext1__cond := GapConfig__ext1O__cond.

Record GapConfig__Type : Set :=
  make__GapConfig__Type {
    GapConfig__gapOffset : Z ;
    GapConfig__mgl : GapConfig__mgl__Type ;
    GapConfig__mgrp : GapConfig__mgrp__Type ;
    GapConfig__mgta : GapConfig__mgta__Type ;
    GapConfig__ext0 : option GapConfig__ext0__Type ;
    GapConfig__ext1 : option GapConfig__ext1__Type ;
}.
Definition GapConfig__root_list : list seq_elem := (
 Nor Z GapConfig__gapOffset__cond ::
 Nor GapConfig__mgl__Type GapConfig__mgl__cond ::
 Nor GapConfig__mgrp__Type GapConfig__mgrp__cond ::
 Nor GapConfig__mgta__Type GapConfig__mgta__cond ::
 nil).
Definition GapConfig__ext_list : list typ := (
  typ_cons GapConfig__ext0__Type GapConfig__ext0__cond ::
  typ_cons GapConfig__ext1__Type GapConfig__ext1__cond ::
  nil).
Definition GapConfig__cond (z : GapConfig__Type) := 
(  GapConfig__gapOffset__cond (GapConfig__gapOffset z) /\
  GapConfig__mgl__cond (GapConfig__mgl z) /\
  GapConfig__mgrp__cond (GapConfig__mgrp z) /\
  GapConfig__mgta__cond (GapConfig__mgta z) /\
  True) /\ 
(  opt_cond GapConfig__ext0__cond (GapConfig__ext0 z) /\
  opt_cond GapConfig__ext1__cond (GapConfig__ext1 z) /\
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
Definition GapConfig__gapOffset__Format : T_Format Z GapConfig__gapOffset__cond :=
 ranged_int_format (0) (159) GapConfig__gapOffset__helper1 GapConfig__gapOffset__helper2.

Opaque GapConfig__gapOffset__cond GapConfig__gapOffset__Format.

Definition GapConfig__mgl__Format : T_Format GapConfig__mgl__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig__mgl__nat__Format GapConfig__mgl__F1 GapConfig__mgl__F2 GapConfig__mgl__F1F2 GapConfig__mgl__F2F1.

Opaque GapConfig__mgl__cond GapConfig__mgl__Format.

Definition GapConfig__mgrp__Format : T_Format GapConfig__mgrp__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig__mgrp__nat__Format GapConfig__mgrp__F1 GapConfig__mgrp__F2 GapConfig__mgrp__F1F2 GapConfig__mgrp__F2F1.

Opaque GapConfig__mgrp__cond GapConfig__mgrp__Format.

Definition GapConfig__mgta__Format : T_Format GapConfig__mgta__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig__mgta__nat__Format GapConfig__mgta__F1 GapConfig__mgta__F2 GapConfig__mgta__F1F2 GapConfig__mgta__F2F1.

Opaque GapConfig__mgta__cond GapConfig__mgta__Format.

Definition GapConfig__ext0O__refServCellIndicator__Format : T_Format GapConfig__ext0O__refServCellIndicator__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig__ext0O__refServCellIndicator__nat__Format GapConfig__ext0O__refServCellIndicator__F1 GapConfig__ext0O__refServCellIndicator__F2 GapConfig__ext0O__refServCellIndicator__F1F2 GapConfig__ext0O__refServCellIndicator__F2F1.

Opaque GapConfig__ext0O__refServCellIndicator__cond GapConfig__ext0O__refServCellIndicator__Format.


Definition GapConfig__ext0O__Format_Type := Eval cbn in seq_format_prod GapConfig__ext0O__list.
Definition GapConfig__ext0O__Format_list : GapConfig__ext0O__Format_Type :=
  (GapConfig__ext0O__refServCellIndicator__Format, unit_format).
Definition GapConfig__ext0O__list__Format := (*Eval compute in *) seq_format GapConfig__ext0O__list GapConfig__ext0O__Format_list.
Definition GapConfig__ext0O__F1 z :=
  (GapConfig__ext0O__refServCellIndicator z, tt).
Definition GapConfig__ext0O__F2 (y : seq_type GapConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__GapConfig__ext0O__Type i0
  end.
Lemma GapConfig__ext0O__F1F2_cond (z : GapConfig__ext0O__Type)
  : GapConfig__ext0O__cond z ->
  (seq_cond GapConfig__ext0O__list (GapConfig__ext0O__F1 z)).
intro H. unfold GapConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma GapConfig__ext0O__F1F2_cond2 (z : GapConfig__ext0O__Type)
 : GapConfig__ext0O__F2 (GapConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma GapConfig__ext0O__F2F1_cond (y : seq_type GapConfig__ext0O__list)
  : seq_cond GapConfig__ext0O__list y ->
 (GapConfig__ext0O__cond (GapConfig__ext0O__F2 y)) /\  GapConfig__ext0O__F1 (GapConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold GapConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold GapConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition GapConfig__ext0O__Format : T_Format GapConfig__ext0O__Type GapConfig__ext0O__cond :=
        proj2_format  GapConfig__ext0O__cond GapConfig__ext0O__list__Format
    GapConfig__ext0O__F1 GapConfig__ext0O__F2 GapConfig__ext0O__F1F2_cond  GapConfig__ext0O__F1F2_cond2 GapConfig__ext0O__F2F1_cond.
Opaque GapConfig__ext0O__cond GapConfig__ext0O__Format.

Definition GapConfig__ext0__check_all_none (b : GapConfig__ext0O__Type) : bool :=
match b with 
  | make__GapConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition GapConfig__ext0__Format : T_Format GapConfig__ext0__Type GapConfig__ext0__cond :=
  restrict_add_format GapConfig__ext0__check_all_none GapConfig__ext0O__Format.

Opaque GapConfig__ext0__cond GapConfig__ext0__Format.

Definition GapConfig__ext1O__mgl_r16__Format : T_Format GapConfig__ext1O__mgl_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig__ext1O__mgl_r16__nat__Format GapConfig__ext1O__mgl_r16__F1 GapConfig__ext1O__mgl_r16__F2 GapConfig__ext1O__mgl_r16__F1F2 GapConfig__ext1O__mgl_r16__F2F1.

Opaque GapConfig__ext1O__mgl_r16__cond GapConfig__ext1O__mgl_r16__Format.


Definition GapConfig__ext1O__Format_Type := Eval cbn in seq_format_prod GapConfig__ext1O__list.
Definition GapConfig__ext1O__Format_list : GapConfig__ext1O__Format_Type :=
  (ServCellIndex__Format, (GapConfig__ext1O__mgl_r16__Format, unit_format)).
Definition GapConfig__ext1O__list__Format := (*Eval compute in *) seq_format GapConfig__ext1O__list GapConfig__ext1O__Format_list.
Definition GapConfig__ext1O__F1 z :=
  (GapConfig__ext1O__refFR2ServCellAsyncCA_r16 z, (GapConfig__ext1O__mgl_r16 z, tt)).
Definition GapConfig__ext1O__F2 (y : seq_type GapConfig__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__GapConfig__ext1O__Type i0 i1
  end.
Lemma GapConfig__ext1O__F1F2_cond (z : GapConfig__ext1O__Type)
  : GapConfig__ext1O__cond z ->
  (seq_cond GapConfig__ext1O__list (GapConfig__ext1O__F1 z)).
intro H. unfold GapConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma GapConfig__ext1O__F1F2_cond2 (z : GapConfig__ext1O__Type)
 : GapConfig__ext1O__F2 (GapConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma GapConfig__ext1O__F2F1_cond (y : seq_type GapConfig__ext1O__list)
  : seq_cond GapConfig__ext1O__list y ->
 (GapConfig__ext1O__cond (GapConfig__ext1O__F2 y)) /\  GapConfig__ext1O__F1 (GapConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold GapConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold GapConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition GapConfig__ext1O__Format : T_Format GapConfig__ext1O__Type GapConfig__ext1O__cond :=
        proj2_format  GapConfig__ext1O__cond GapConfig__ext1O__list__Format
    GapConfig__ext1O__F1 GapConfig__ext1O__F2 GapConfig__ext1O__F1F2_cond  GapConfig__ext1O__F1F2_cond2 GapConfig__ext1O__F2F1_cond.
Opaque GapConfig__ext1O__cond GapConfig__ext1O__Format.

Definition GapConfig__ext1__check_all_none (b : GapConfig__ext1O__Type) : bool :=
match b with 
  | make__GapConfig__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition GapConfig__ext1__Format : T_Format GapConfig__ext1__Type GapConfig__ext1__cond :=
  restrict_add_format GapConfig__ext1__check_all_none GapConfig__ext1O__Format.

Opaque GapConfig__ext1__cond GapConfig__ext1__Format.


Definition GapConfig__root_Format_Type := Eval cbn in seq_format_prod GapConfig__root_list.
Definition GapConfig__root_Format_list : GapConfig__root_Format_Type :=
  (GapConfig__gapOffset__Format, (GapConfig__mgl__Format, (GapConfig__mgrp__Format, (GapConfig__mgta__Format, unit_format)))).

Definition GapConfig__ext_Format_Type := Eval cbn in get_formats GapConfig__ext_list.
Definition GapConfig__ext_Format_list : GapConfig__ext_Format_Type :=
  (GapConfig__ext0__Format, (GapConfig__ext1__Format, unit__Format)).

Definition GapConfig__list_type : Set := (seq_type GapConfig__root_list) * (seq_ext_type GapConfig__ext_list).
Definition GapConfig__list_cond (z : GapConfig__list_type) : Prop :=
        (seq_cond GapConfig__root_list (fst z)) /\ (seq_ext_cond GapConfig__ext_list (snd z)).
Definition GapConfig__list_format : T_Format GapConfig__list_type GapConfig__list_cond :=
 (* Eval compute in *) seq_ext_format GapConfig__root_list GapConfig__root_Format_list GapConfig__ext_list GapConfig__ext_Format_list.

Opaque GapConfig__list_format.
Definition GapConfig__F1 (z : GapConfig__Type) : GapConfig__list_type :=
  (((GapConfig__gapOffset z, (GapConfig__mgl z, (GapConfig__mgrp z, (GapConfig__mgta z, tt))))), (
(GapConfig__ext0 z, (GapConfig__ext1 z, tt)))).
Definition GapConfig__F2 (y : GapConfig__list_type) : GapConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__GapConfig__Type j0 j1 j2 j3 i0 i1
  end.
Definition GapConfig__helper1 : (forall a : GapConfig__Type, GapConfig__cond a -> GapConfig__list_cond (GapConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition GapConfig__helper2 : (forall a : GapConfig__Type, GapConfig__F2 (GapConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition GapConfig__helper3 : (forall b : GapConfig__list_type, GapConfig__list_cond b -> GapConfig__cond (GapConfig__F2 b) /\ GapConfig__F1 (GapConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold GapConfig__cond, GapConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition GapConfig__Format : T_Format GapConfig__Type GapConfig__cond :=
 proj2_format GapConfig__cond GapConfig__list_format  GapConfig__F1 GapConfig__F2 GapConfig__helper1 GapConfig__helper2 GapConfig__helper3.

Opaque GapConfig__cond GapConfig__Format.

