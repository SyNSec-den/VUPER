Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.InterFreqCarrierFreqList.

Opaque InterFreqCarrierFreqList__cond InterFreqCarrierFreqList__Format.

Require Import NR.InterFreqCarrierFreqList_v1610.

Opaque InterFreqCarrierFreqList_v1610__cond InterFreqCarrierFreqList_v1610__Format.

Record SIB4__ext0O__Type : Set :=
  make__SIB4__ext0O__Type {
    SIB4__ext0O__interFreqCarrierFreqList_v1610 : option InterFreqCarrierFreqList_v1610__Type ;
}.
Definition SIB4__ext0O__list := (
 Opt InterFreqCarrierFreqList_v1610__Type InterFreqCarrierFreqList_v1610__cond ::
 nil).
Definition SIB4__ext0O__cond z := 
  opt_cond InterFreqCarrierFreqList_v1610__cond (SIB4__ext0O__interFreqCarrierFreqList_v1610 z) /\
  True.

Definition SIB4__ext0__Type := SIB4__ext0O__Type.
Definition SIB4__ext0__cond := SIB4__ext0O__cond.

Require Import NR.InterFreqCarrierFreqList_v1700.

Opaque InterFreqCarrierFreqList_v1700__cond InterFreqCarrierFreqList_v1700__Format.

Record SIB4__ext1O__Type : Set :=
  make__SIB4__ext1O__Type {
    SIB4__ext1O__interFreqCarrierFreqList_v1700 : option InterFreqCarrierFreqList_v1700__Type ;
}.
Definition SIB4__ext1O__list := (
 Opt InterFreqCarrierFreqList_v1700__Type InterFreqCarrierFreqList_v1700__cond ::
 nil).
Definition SIB4__ext1O__cond z := 
  opt_cond InterFreqCarrierFreqList_v1700__cond (SIB4__ext1O__interFreqCarrierFreqList_v1700 z) /\
  True.

Definition SIB4__ext1__Type := SIB4__ext1O__Type.
Definition SIB4__ext1__cond := SIB4__ext1O__cond.

Require Import NR.InterFreqCarrierFreqList_v1720.

Opaque InterFreqCarrierFreqList_v1720__cond InterFreqCarrierFreqList_v1720__Format.

Record SIB4__ext2O__Type : Set :=
  make__SIB4__ext2O__Type {
    SIB4__ext2O__interFreqCarrierFreqList_v1720 : option InterFreqCarrierFreqList_v1720__Type ;
}.
Definition SIB4__ext2O__list := (
 Opt InterFreqCarrierFreqList_v1720__Type InterFreqCarrierFreqList_v1720__cond ::
 nil).
Definition SIB4__ext2O__cond z := 
  opt_cond InterFreqCarrierFreqList_v1720__cond (SIB4__ext2O__interFreqCarrierFreqList_v1720 z) /\
  True.

Definition SIB4__ext2__Type := SIB4__ext2O__Type.
Definition SIB4__ext2__cond := SIB4__ext2O__cond.

Require Import NR.InterFreqCarrierFreqList_v1730.

Opaque InterFreqCarrierFreqList_v1730__cond InterFreqCarrierFreqList_v1730__Format.

Record SIB4__ext3O__Type : Set :=
  make__SIB4__ext3O__Type {
    SIB4__ext3O__interFreqCarrierFreqList_v1730 : option InterFreqCarrierFreqList_v1730__Type ;
}.
Definition SIB4__ext3O__list := (
 Opt InterFreqCarrierFreqList_v1730__Type InterFreqCarrierFreqList_v1730__cond ::
 nil).
Definition SIB4__ext3O__cond z := 
  opt_cond InterFreqCarrierFreqList_v1730__cond (SIB4__ext3O__interFreqCarrierFreqList_v1730 z) /\
  True.

Definition SIB4__ext3__Type := SIB4__ext3O__Type.
Definition SIB4__ext3__cond := SIB4__ext3O__cond.

Record SIB4__Type : Set :=
  make__SIB4__Type {
    SIB4__interFreqCarrierFreqList : InterFreqCarrierFreqList__Type ;
    SIB4__lateNonCriticalExtension : option octet_string ;
    SIB4__ext0 : option SIB4__ext0__Type ;
    SIB4__ext1 : option SIB4__ext1__Type ;
    SIB4__ext2 : option SIB4__ext2__Type ;
    SIB4__ext3 : option SIB4__ext3__Type ;
}.
Definition SIB4__root_list : list seq_elem := (
 Nor InterFreqCarrierFreqList__Type InterFreqCarrierFreqList__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SIB4__ext_list : list typ := (
  typ_cons SIB4__ext0__Type SIB4__ext0__cond ::
  typ_cons SIB4__ext1__Type SIB4__ext1__cond ::
  typ_cons SIB4__ext2__Type SIB4__ext2__cond ::
  typ_cons SIB4__ext3__Type SIB4__ext3__cond ::
  nil).
Definition SIB4__cond (z : SIB4__Type) := 
(  InterFreqCarrierFreqList__cond (SIB4__interFreqCarrierFreqList z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SIB4__lateNonCriticalExtension z) /\
  True) /\ 
(  opt_cond SIB4__ext0__cond (SIB4__ext0 z) /\
  opt_cond SIB4__ext1__cond (SIB4__ext1 z) /\
  opt_cond SIB4__ext2__cond (SIB4__ext2 z) /\
  opt_cond SIB4__ext3__cond (SIB4__ext3 z) /\
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

Definition SIB4__ext0O__Format_Type := Eval cbn in seq_format_prod SIB4__ext0O__list.
Definition SIB4__ext0O__Format_list : SIB4__ext0O__Format_Type :=
  (InterFreqCarrierFreqList_v1610__Format, unit_format).
Definition SIB4__ext0O__list__Format := (*Eval compute in *) seq_format SIB4__ext0O__list SIB4__ext0O__Format_list.
Definition SIB4__ext0O__F1 z :=
  (SIB4__ext0O__interFreqCarrierFreqList_v1610 z, tt).
Definition SIB4__ext0O__F2 (y : seq_type SIB4__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SIB4__ext0O__Type i0
  end.
Lemma SIB4__ext0O__F1F2_cond (z : SIB4__ext0O__Type)
  : SIB4__ext0O__cond z ->
  (seq_cond SIB4__ext0O__list (SIB4__ext0O__F1 z)).
intro H. unfold SIB4__ext0O__cond in H. simpl. auto. Qed.
Lemma SIB4__ext0O__F1F2_cond2 (z : SIB4__ext0O__Type)
 : SIB4__ext0O__F2 (SIB4__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB4__ext0O__F2F1_cond (y : seq_type SIB4__ext0O__list)
  : seq_cond SIB4__ext0O__list y ->
 (SIB4__ext0O__cond (SIB4__ext0O__F2 y)) /\  SIB4__ext0O__F1 (SIB4__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB4__ext0O__cond. simpl in *. auto.
 - simpl. unfold SIB4__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB4__ext0O__Format : T_Format SIB4__ext0O__Type SIB4__ext0O__cond :=
        proj2_format  SIB4__ext0O__cond SIB4__ext0O__list__Format
    SIB4__ext0O__F1 SIB4__ext0O__F2 SIB4__ext0O__F1F2_cond  SIB4__ext0O__F1F2_cond2 SIB4__ext0O__F2F1_cond.
Opaque SIB4__ext0O__cond SIB4__ext0O__Format.

Definition SIB4__ext0__check_all_none (b : SIB4__ext0O__Type) : bool :=
match b with 
  | make__SIB4__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SIB4__ext0__Format : T_Format SIB4__ext0__Type SIB4__ext0__cond :=
  restrict_add_format SIB4__ext0__check_all_none SIB4__ext0O__Format.

Opaque SIB4__ext0__cond SIB4__ext0__Format.


Definition SIB4__ext1O__Format_Type := Eval cbn in seq_format_prod SIB4__ext1O__list.
Definition SIB4__ext1O__Format_list : SIB4__ext1O__Format_Type :=
  (InterFreqCarrierFreqList_v1700__Format, unit_format).
Definition SIB4__ext1O__list__Format := (*Eval compute in *) seq_format SIB4__ext1O__list SIB4__ext1O__Format_list.
Definition SIB4__ext1O__F1 z :=
  (SIB4__ext1O__interFreqCarrierFreqList_v1700 z, tt).
Definition SIB4__ext1O__F2 (y : seq_type SIB4__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__SIB4__ext1O__Type i0
  end.
Lemma SIB4__ext1O__F1F2_cond (z : SIB4__ext1O__Type)
  : SIB4__ext1O__cond z ->
  (seq_cond SIB4__ext1O__list (SIB4__ext1O__F1 z)).
intro H. unfold SIB4__ext1O__cond in H. simpl. auto. Qed.
Lemma SIB4__ext1O__F1F2_cond2 (z : SIB4__ext1O__Type)
 : SIB4__ext1O__F2 (SIB4__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB4__ext1O__F2F1_cond (y : seq_type SIB4__ext1O__list)
  : seq_cond SIB4__ext1O__list y ->
 (SIB4__ext1O__cond (SIB4__ext1O__F2 y)) /\  SIB4__ext1O__F1 (SIB4__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB4__ext1O__cond. simpl in *. auto.
 - simpl. unfold SIB4__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB4__ext1O__Format : T_Format SIB4__ext1O__Type SIB4__ext1O__cond :=
        proj2_format  SIB4__ext1O__cond SIB4__ext1O__list__Format
    SIB4__ext1O__F1 SIB4__ext1O__F2 SIB4__ext1O__F1F2_cond  SIB4__ext1O__F1F2_cond2 SIB4__ext1O__F2F1_cond.
Opaque SIB4__ext1O__cond SIB4__ext1O__Format.

Definition SIB4__ext1__check_all_none (b : SIB4__ext1O__Type) : bool :=
match b with 
  | make__SIB4__ext1O__Type None  => false 
  | _ => true 
 end.
Definition SIB4__ext1__Format : T_Format SIB4__ext1__Type SIB4__ext1__cond :=
  restrict_add_format SIB4__ext1__check_all_none SIB4__ext1O__Format.

Opaque SIB4__ext1__cond SIB4__ext1__Format.


Definition SIB4__ext2O__Format_Type := Eval cbn in seq_format_prod SIB4__ext2O__list.
Definition SIB4__ext2O__Format_list : SIB4__ext2O__Format_Type :=
  (InterFreqCarrierFreqList_v1720__Format, unit_format).
Definition SIB4__ext2O__list__Format := (*Eval compute in *) seq_format SIB4__ext2O__list SIB4__ext2O__Format_list.
Definition SIB4__ext2O__F1 z :=
  (SIB4__ext2O__interFreqCarrierFreqList_v1720 z, tt).
Definition SIB4__ext2O__F2 (y : seq_type SIB4__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__SIB4__ext2O__Type i0
  end.
Lemma SIB4__ext2O__F1F2_cond (z : SIB4__ext2O__Type)
  : SIB4__ext2O__cond z ->
  (seq_cond SIB4__ext2O__list (SIB4__ext2O__F1 z)).
intro H. unfold SIB4__ext2O__cond in H. simpl. auto. Qed.
Lemma SIB4__ext2O__F1F2_cond2 (z : SIB4__ext2O__Type)
 : SIB4__ext2O__F2 (SIB4__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB4__ext2O__F2F1_cond (y : seq_type SIB4__ext2O__list)
  : seq_cond SIB4__ext2O__list y ->
 (SIB4__ext2O__cond (SIB4__ext2O__F2 y)) /\  SIB4__ext2O__F1 (SIB4__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB4__ext2O__cond. simpl in *. auto.
 - simpl. unfold SIB4__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB4__ext2O__Format : T_Format SIB4__ext2O__Type SIB4__ext2O__cond :=
        proj2_format  SIB4__ext2O__cond SIB4__ext2O__list__Format
    SIB4__ext2O__F1 SIB4__ext2O__F2 SIB4__ext2O__F1F2_cond  SIB4__ext2O__F1F2_cond2 SIB4__ext2O__F2F1_cond.
Opaque SIB4__ext2O__cond SIB4__ext2O__Format.

Definition SIB4__ext2__check_all_none (b : SIB4__ext2O__Type) : bool :=
match b with 
  | make__SIB4__ext2O__Type None  => false 
  | _ => true 
 end.
Definition SIB4__ext2__Format : T_Format SIB4__ext2__Type SIB4__ext2__cond :=
  restrict_add_format SIB4__ext2__check_all_none SIB4__ext2O__Format.

Opaque SIB4__ext2__cond SIB4__ext2__Format.


Definition SIB4__ext3O__Format_Type := Eval cbn in seq_format_prod SIB4__ext3O__list.
Definition SIB4__ext3O__Format_list : SIB4__ext3O__Format_Type :=
  (InterFreqCarrierFreqList_v1730__Format, unit_format).
Definition SIB4__ext3O__list__Format := (*Eval compute in *) seq_format SIB4__ext3O__list SIB4__ext3O__Format_list.
Definition SIB4__ext3O__F1 z :=
  (SIB4__ext3O__interFreqCarrierFreqList_v1730 z, tt).
Definition SIB4__ext3O__F2 (y : seq_type SIB4__ext3O__list) :=
  match y with
  | (i0, _)=>
    make__SIB4__ext3O__Type i0
  end.
Lemma SIB4__ext3O__F1F2_cond (z : SIB4__ext3O__Type)
  : SIB4__ext3O__cond z ->
  (seq_cond SIB4__ext3O__list (SIB4__ext3O__F1 z)).
intro H. unfold SIB4__ext3O__cond in H. simpl. auto. Qed.
Lemma SIB4__ext3O__F1F2_cond2 (z : SIB4__ext3O__Type)
 : SIB4__ext3O__F2 (SIB4__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB4__ext3O__F2F1_cond (y : seq_type SIB4__ext3O__list)
  : seq_cond SIB4__ext3O__list y ->
 (SIB4__ext3O__cond (SIB4__ext3O__F2 y)) /\  SIB4__ext3O__F1 (SIB4__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB4__ext3O__cond. simpl in *. auto.
 - simpl. unfold SIB4__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB4__ext3O__Format : T_Format SIB4__ext3O__Type SIB4__ext3O__cond :=
        proj2_format  SIB4__ext3O__cond SIB4__ext3O__list__Format
    SIB4__ext3O__F1 SIB4__ext3O__F2 SIB4__ext3O__F1F2_cond  SIB4__ext3O__F1F2_cond2 SIB4__ext3O__F2F1_cond.
Opaque SIB4__ext3O__cond SIB4__ext3O__Format.

Definition SIB4__ext3__check_all_none (b : SIB4__ext3O__Type) : bool :=
match b with 
  | make__SIB4__ext3O__Type None  => false 
  | _ => true 
 end.
Definition SIB4__ext3__Format : T_Format SIB4__ext3__Type SIB4__ext3__cond :=
  restrict_add_format SIB4__ext3__check_all_none SIB4__ext3O__Format.

Opaque SIB4__ext3__cond SIB4__ext3__Format.


Definition SIB4__root_Format_Type := Eval cbn in seq_format_prod SIB4__root_list.
Definition SIB4__root_Format_list : SIB4__root_Format_Type :=
  (InterFreqCarrierFreqList__Format, (octet_string_nc__Format, unit_format)).

Definition SIB4__ext_Format_Type := Eval cbn in get_formats SIB4__ext_list.
Definition SIB4__ext_Format_list : SIB4__ext_Format_Type :=
  (SIB4__ext0__Format, (SIB4__ext1__Format, (SIB4__ext2__Format, (SIB4__ext3__Format, unit__Format)))).

Definition SIB4__list_type : Set := (seq_type SIB4__root_list) * (seq_ext_type SIB4__ext_list).
Definition SIB4__list_cond (z : SIB4__list_type) : Prop :=
        (seq_cond SIB4__root_list (fst z)) /\ (seq_ext_cond SIB4__ext_list (snd z)).
Definition SIB4__list_format : T_Format SIB4__list_type SIB4__list_cond :=
 (* Eval compute in *) seq_ext_format SIB4__root_list SIB4__root_Format_list SIB4__ext_list SIB4__ext_Format_list.

Opaque SIB4__list_format.
Definition SIB4__F1 (z : SIB4__Type) : SIB4__list_type :=
  (((SIB4__interFreqCarrierFreqList z, (SIB4__lateNonCriticalExtension z, tt))), (
(SIB4__ext0 z, (SIB4__ext1 z, (SIB4__ext2 z, (SIB4__ext3 z, tt)))))).
Definition SIB4__F2 (y : SIB4__list_type) : SIB4__Type :=
  match y with
  | ((j0, (j1, _)), (i0, (i1, (i2, (i3, _)))))=>
    make__SIB4__Type j0 j1 i0 i1 i2 i3
  end.
Definition SIB4__helper1 : (forall a : SIB4__Type, SIB4__cond a -> SIB4__list_cond (SIB4__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB4__helper2 : (forall a : SIB4__Type, SIB4__F2 (SIB4__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB4__helper3 : (forall b : SIB4__list_type, SIB4__list_cond b -> SIB4__cond (SIB4__F2 b) /\ SIB4__F1 (SIB4__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB4__cond, SIB4__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB4__Format : T_Format SIB4__Type SIB4__cond :=
 proj2_format SIB4__cond SIB4__list_format  SIB4__F1 SIB4__F2 SIB4__helper1 SIB4__helper2 SIB4__helper3.

Opaque SIB4__cond SIB4__Format.

