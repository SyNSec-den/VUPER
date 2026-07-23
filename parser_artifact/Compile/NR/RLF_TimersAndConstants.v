Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RLF_TimersAndConstants__t310__Type : Set :=
 | RLF_TimersAndConstants__t310__ms0
 | RLF_TimersAndConstants__t310__ms50
 | RLF_TimersAndConstants__t310__ms100
 | RLF_TimersAndConstants__t310__ms200
 | RLF_TimersAndConstants__t310__ms500
 | RLF_TimersAndConstants__t310__ms1000
 | RLF_TimersAndConstants__t310__ms2000
 | RLF_TimersAndConstants__t310__ms4000
 | RLF_TimersAndConstants__t310__ms6000
.
Definition RLF_TimersAndConstants__t310__cond := (fun (_ : RLF_TimersAndConstants__t310__Type) => True).
Lemma RLF_TimersAndConstants__t310__nat__helper : to_bit_sz 8 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLF_TimersAndConstants__t310__nat__Format : T_Format nat (fun z => (z <= 8)) :=
  nat_enum_format 8 RLF_TimersAndConstants__t310__nat__helper.

Definition RLF_TimersAndConstants__t310__F1 t :=
  match t with
  | RLF_TimersAndConstants__t310__ms0 => 0
  | RLF_TimersAndConstants__t310__ms50 => 1
  | RLF_TimersAndConstants__t310__ms100 => 2
  | RLF_TimersAndConstants__t310__ms200 => 3
  | RLF_TimersAndConstants__t310__ms500 => 4
  | RLF_TimersAndConstants__t310__ms1000 => 5
  | RLF_TimersAndConstants__t310__ms2000 => 6
  | RLF_TimersAndConstants__t310__ms4000 => 7
  | RLF_TimersAndConstants__t310__ms6000 => 8
  end.
Definition RLF_TimersAndConstants__t310__F2 n :=
  match n with
  | 0 => RLF_TimersAndConstants__t310__ms0
  | 1 => RLF_TimersAndConstants__t310__ms50
  | 2 => RLF_TimersAndConstants__t310__ms100
  | 3 => RLF_TimersAndConstants__t310__ms200
  | 4 => RLF_TimersAndConstants__t310__ms500
  | 5 => RLF_TimersAndConstants__t310__ms1000
  | 6 => RLF_TimersAndConstants__t310__ms2000
  | 7 => RLF_TimersAndConstants__t310__ms4000
  | 8 => RLF_TimersAndConstants__t310__ms6000
  | _ => RLF_TimersAndConstants__t310__ms0
  end.
Lemma RLF_TimersAndConstants__t310__F1F2 : forall x : RLF_TimersAndConstants__t310__Type, (RLF_TimersAndConstants__t310__F1 x <= 8) /\ RLF_TimersAndConstants__t310__F2 (RLF_TimersAndConstants__t310__F1 x) = x. imp_solve. Qed.
Lemma RLF_TimersAndConstants__t310__F2F1 : forall (y : nat) (H : y <= 8), RLF_TimersAndConstants__t310__F1 (RLF_TimersAndConstants__t310__F2 y) = y. enum_solve H y. Qed.

Inductive RLF_TimersAndConstants__n310__Type : Set :=
 | RLF_TimersAndConstants__n310__n1
 | RLF_TimersAndConstants__n310__n2
 | RLF_TimersAndConstants__n310__n3
 | RLF_TimersAndConstants__n310__n4
 | RLF_TimersAndConstants__n310__n6
 | RLF_TimersAndConstants__n310__n8
 | RLF_TimersAndConstants__n310__n10
 | RLF_TimersAndConstants__n310__n20
.
Definition RLF_TimersAndConstants__n310__cond := (fun (_ : RLF_TimersAndConstants__n310__Type) => True).
Lemma RLF_TimersAndConstants__n310__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLF_TimersAndConstants__n310__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RLF_TimersAndConstants__n310__nat__helper.

Definition RLF_TimersAndConstants__n310__F1 t :=
  match t with
  | RLF_TimersAndConstants__n310__n1 => 0
  | RLF_TimersAndConstants__n310__n2 => 1
  | RLF_TimersAndConstants__n310__n3 => 2
  | RLF_TimersAndConstants__n310__n4 => 3
  | RLF_TimersAndConstants__n310__n6 => 4
  | RLF_TimersAndConstants__n310__n8 => 5
  | RLF_TimersAndConstants__n310__n10 => 6
  | RLF_TimersAndConstants__n310__n20 => 7
  end.
Definition RLF_TimersAndConstants__n310__F2 n :=
  match n with
  | 0 => RLF_TimersAndConstants__n310__n1
  | 1 => RLF_TimersAndConstants__n310__n2
  | 2 => RLF_TimersAndConstants__n310__n3
  | 3 => RLF_TimersAndConstants__n310__n4
  | 4 => RLF_TimersAndConstants__n310__n6
  | 5 => RLF_TimersAndConstants__n310__n8
  | 6 => RLF_TimersAndConstants__n310__n10
  | 7 => RLF_TimersAndConstants__n310__n20
  | _ => RLF_TimersAndConstants__n310__n1
  end.
Lemma RLF_TimersAndConstants__n310__F1F2 : forall x : RLF_TimersAndConstants__n310__Type, (RLF_TimersAndConstants__n310__F1 x <= 7) /\ RLF_TimersAndConstants__n310__F2 (RLF_TimersAndConstants__n310__F1 x) = x. imp_solve. Qed.
Lemma RLF_TimersAndConstants__n310__F2F1 : forall (y : nat) (H : y <= 7), RLF_TimersAndConstants__n310__F1 (RLF_TimersAndConstants__n310__F2 y) = y. enum_solve H y. Qed.

Inductive RLF_TimersAndConstants__n311__Type : Set :=
 | RLF_TimersAndConstants__n311__n1
 | RLF_TimersAndConstants__n311__n2
 | RLF_TimersAndConstants__n311__n3
 | RLF_TimersAndConstants__n311__n4
 | RLF_TimersAndConstants__n311__n5
 | RLF_TimersAndConstants__n311__n6
 | RLF_TimersAndConstants__n311__n8
 | RLF_TimersAndConstants__n311__n10
.
Definition RLF_TimersAndConstants__n311__cond := (fun (_ : RLF_TimersAndConstants__n311__Type) => True).
Lemma RLF_TimersAndConstants__n311__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLF_TimersAndConstants__n311__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RLF_TimersAndConstants__n311__nat__helper.

Definition RLF_TimersAndConstants__n311__F1 t :=
  match t with
  | RLF_TimersAndConstants__n311__n1 => 0
  | RLF_TimersAndConstants__n311__n2 => 1
  | RLF_TimersAndConstants__n311__n3 => 2
  | RLF_TimersAndConstants__n311__n4 => 3
  | RLF_TimersAndConstants__n311__n5 => 4
  | RLF_TimersAndConstants__n311__n6 => 5
  | RLF_TimersAndConstants__n311__n8 => 6
  | RLF_TimersAndConstants__n311__n10 => 7
  end.
Definition RLF_TimersAndConstants__n311__F2 n :=
  match n with
  | 0 => RLF_TimersAndConstants__n311__n1
  | 1 => RLF_TimersAndConstants__n311__n2
  | 2 => RLF_TimersAndConstants__n311__n3
  | 3 => RLF_TimersAndConstants__n311__n4
  | 4 => RLF_TimersAndConstants__n311__n5
  | 5 => RLF_TimersAndConstants__n311__n6
  | 6 => RLF_TimersAndConstants__n311__n8
  | 7 => RLF_TimersAndConstants__n311__n10
  | _ => RLF_TimersAndConstants__n311__n1
  end.
Lemma RLF_TimersAndConstants__n311__F1F2 : forall x : RLF_TimersAndConstants__n311__Type, (RLF_TimersAndConstants__n311__F1 x <= 7) /\ RLF_TimersAndConstants__n311__F2 (RLF_TimersAndConstants__n311__F1 x) = x. imp_solve. Qed.
Lemma RLF_TimersAndConstants__n311__F2F1 : forall (y : nat) (H : y <= 7), RLF_TimersAndConstants__n311__F1 (RLF_TimersAndConstants__n311__F2 y) = y. enum_solve H y. Qed.

Inductive RLF_TimersAndConstants__ext0__t311__Type : Set :=
 | RLF_TimersAndConstants__ext0__t311__ms1000
 | RLF_TimersAndConstants__ext0__t311__ms3000
 | RLF_TimersAndConstants__ext0__t311__ms5000
 | RLF_TimersAndConstants__ext0__t311__ms10000
 | RLF_TimersAndConstants__ext0__t311__ms15000
 | RLF_TimersAndConstants__ext0__t311__ms20000
 | RLF_TimersAndConstants__ext0__t311__ms30000
.
Definition RLF_TimersAndConstants__ext0__t311__cond := (fun (_ : RLF_TimersAndConstants__ext0__t311__Type) => True).
Lemma RLF_TimersAndConstants__ext0__t311__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLF_TimersAndConstants__ext0__t311__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 RLF_TimersAndConstants__ext0__t311__nat__helper.

Definition RLF_TimersAndConstants__ext0__t311__F1 t :=
  match t with
  | RLF_TimersAndConstants__ext0__t311__ms1000 => 0
  | RLF_TimersAndConstants__ext0__t311__ms3000 => 1
  | RLF_TimersAndConstants__ext0__t311__ms5000 => 2
  | RLF_TimersAndConstants__ext0__t311__ms10000 => 3
  | RLF_TimersAndConstants__ext0__t311__ms15000 => 4
  | RLF_TimersAndConstants__ext0__t311__ms20000 => 5
  | RLF_TimersAndConstants__ext0__t311__ms30000 => 6
  end.
Definition RLF_TimersAndConstants__ext0__t311__F2 n :=
  match n with
  | 0 => RLF_TimersAndConstants__ext0__t311__ms1000
  | 1 => RLF_TimersAndConstants__ext0__t311__ms3000
  | 2 => RLF_TimersAndConstants__ext0__t311__ms5000
  | 3 => RLF_TimersAndConstants__ext0__t311__ms10000
  | 4 => RLF_TimersAndConstants__ext0__t311__ms15000
  | 5 => RLF_TimersAndConstants__ext0__t311__ms20000
  | 6 => RLF_TimersAndConstants__ext0__t311__ms30000
  | _ => RLF_TimersAndConstants__ext0__t311__ms1000
  end.
Lemma RLF_TimersAndConstants__ext0__t311__F1F2 : forall x : RLF_TimersAndConstants__ext0__t311__Type, (RLF_TimersAndConstants__ext0__t311__F1 x <= 6) /\ RLF_TimersAndConstants__ext0__t311__F2 (RLF_TimersAndConstants__ext0__t311__F1 x) = x. imp_solve. Qed.
Lemma RLF_TimersAndConstants__ext0__t311__F2F1 : forall (y : nat) (H : y <= 6), RLF_TimersAndConstants__ext0__t311__F1 (RLF_TimersAndConstants__ext0__t311__F2 y) = y. enum_solve H y. Qed.

Record RLF_TimersAndConstants__ext0__Type : Set :=
  make__RLF_TimersAndConstants__ext0__Type {
    RLF_TimersAndConstants__ext0__t311 : RLF_TimersAndConstants__ext0__t311__Type ;
}.
Definition RLF_TimersAndConstants__ext0__list := (
 Nor RLF_TimersAndConstants__ext0__t311__Type RLF_TimersAndConstants__ext0__t311__cond ::
 nil).
Definition RLF_TimersAndConstants__ext0__cond z := 
  RLF_TimersAndConstants__ext0__t311__cond (RLF_TimersAndConstants__ext0__t311 z) /\
  True.

Record RLF_TimersAndConstants__Type : Set :=
  make__RLF_TimersAndConstants__Type {
    RLF_TimersAndConstants__t310 : RLF_TimersAndConstants__t310__Type ;
    RLF_TimersAndConstants__n310 : RLF_TimersAndConstants__n310__Type ;
    RLF_TimersAndConstants__n311 : RLF_TimersAndConstants__n311__Type ;
    RLF_TimersAndConstants__ext0 : option RLF_TimersAndConstants__ext0__Type ;
}.
Definition RLF_TimersAndConstants__root_list : list seq_elem := (
 Nor RLF_TimersAndConstants__t310__Type RLF_TimersAndConstants__t310__cond ::
 Nor RLF_TimersAndConstants__n310__Type RLF_TimersAndConstants__n310__cond ::
 Nor RLF_TimersAndConstants__n311__Type RLF_TimersAndConstants__n311__cond ::
 nil).
Definition RLF_TimersAndConstants__ext_list : list typ := (
  typ_cons RLF_TimersAndConstants__ext0__Type RLF_TimersAndConstants__ext0__cond ::
  nil).
Definition RLF_TimersAndConstants__cond (z : RLF_TimersAndConstants__Type) := 
(  RLF_TimersAndConstants__t310__cond (RLF_TimersAndConstants__t310 z) /\
  RLF_TimersAndConstants__n310__cond (RLF_TimersAndConstants__n310 z) /\
  RLF_TimersAndConstants__n311__cond (RLF_TimersAndConstants__n311 z) /\
  True) /\ 
(  opt_cond RLF_TimersAndConstants__ext0__cond (RLF_TimersAndConstants__ext0 z) /\
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
Definition RLF_TimersAndConstants__t310__Format : T_Format RLF_TimersAndConstants__t310__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLF_TimersAndConstants__t310__nat__Format RLF_TimersAndConstants__t310__F1 RLF_TimersAndConstants__t310__F2 RLF_TimersAndConstants__t310__F1F2 RLF_TimersAndConstants__t310__F2F1.

Opaque RLF_TimersAndConstants__t310__cond RLF_TimersAndConstants__t310__Format.

Definition RLF_TimersAndConstants__n310__Format : T_Format RLF_TimersAndConstants__n310__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLF_TimersAndConstants__n310__nat__Format RLF_TimersAndConstants__n310__F1 RLF_TimersAndConstants__n310__F2 RLF_TimersAndConstants__n310__F1F2 RLF_TimersAndConstants__n310__F2F1.

Opaque RLF_TimersAndConstants__n310__cond RLF_TimersAndConstants__n310__Format.

Definition RLF_TimersAndConstants__n311__Format : T_Format RLF_TimersAndConstants__n311__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLF_TimersAndConstants__n311__nat__Format RLF_TimersAndConstants__n311__F1 RLF_TimersAndConstants__n311__F2 RLF_TimersAndConstants__n311__F1F2 RLF_TimersAndConstants__n311__F2F1.

Opaque RLF_TimersAndConstants__n311__cond RLF_TimersAndConstants__n311__Format.

Definition RLF_TimersAndConstants__ext0__t311__Format : T_Format RLF_TimersAndConstants__ext0__t311__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLF_TimersAndConstants__ext0__t311__nat__Format RLF_TimersAndConstants__ext0__t311__F1 RLF_TimersAndConstants__ext0__t311__F2 RLF_TimersAndConstants__ext0__t311__F1F2 RLF_TimersAndConstants__ext0__t311__F2F1.

Opaque RLF_TimersAndConstants__ext0__t311__cond RLF_TimersAndConstants__ext0__t311__Format.


Definition RLF_TimersAndConstants__ext0__Format_Type := Eval cbn in seq_format_prod RLF_TimersAndConstants__ext0__list.
Definition RLF_TimersAndConstants__ext0__Format_list : RLF_TimersAndConstants__ext0__Format_Type :=
  (RLF_TimersAndConstants__ext0__t311__Format, unit_format).
Definition RLF_TimersAndConstants__ext0__list__Format := (*Eval compute in *) seq_format RLF_TimersAndConstants__ext0__list RLF_TimersAndConstants__ext0__Format_list.
Definition RLF_TimersAndConstants__ext0__F1 z :=
  (RLF_TimersAndConstants__ext0__t311 z, tt).
Definition RLF_TimersAndConstants__ext0__F2 (y : seq_type RLF_TimersAndConstants__ext0__list) :=
  match y with
  | (i0, _)=>
    make__RLF_TimersAndConstants__ext0__Type i0
  end.
Lemma RLF_TimersAndConstants__ext0__F1F2_cond (z : RLF_TimersAndConstants__ext0__Type)
  : RLF_TimersAndConstants__ext0__cond z ->
  (seq_cond RLF_TimersAndConstants__ext0__list (RLF_TimersAndConstants__ext0__F1 z)).
intro H. unfold RLF_TimersAndConstants__ext0__cond in H. simpl. auto. Qed.
Lemma RLF_TimersAndConstants__ext0__F1F2_cond2 (z : RLF_TimersAndConstants__ext0__Type)
 : RLF_TimersAndConstants__ext0__F2 (RLF_TimersAndConstants__ext0__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLF_TimersAndConstants__ext0__F2F1_cond (y : seq_type RLF_TimersAndConstants__ext0__list)
  : seq_cond RLF_TimersAndConstants__ext0__list y ->
 (RLF_TimersAndConstants__ext0__cond (RLF_TimersAndConstants__ext0__F2 y)) /\  RLF_TimersAndConstants__ext0__F1 (RLF_TimersAndConstants__ext0__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLF_TimersAndConstants__ext0__cond. simpl in *. auto.
 - simpl. unfold RLF_TimersAndConstants__ext0__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLF_TimersAndConstants__ext0__Format : T_Format RLF_TimersAndConstants__ext0__Type RLF_TimersAndConstants__ext0__cond :=
        proj2_format  RLF_TimersAndConstants__ext0__cond RLF_TimersAndConstants__ext0__list__Format
    RLF_TimersAndConstants__ext0__F1 RLF_TimersAndConstants__ext0__F2 RLF_TimersAndConstants__ext0__F1F2_cond  RLF_TimersAndConstants__ext0__F1F2_cond2 RLF_TimersAndConstants__ext0__F2F1_cond.
Opaque RLF_TimersAndConstants__ext0__cond RLF_TimersAndConstants__ext0__Format.


Definition RLF_TimersAndConstants__root_Format_Type := Eval cbn in seq_format_prod RLF_TimersAndConstants__root_list.
Definition RLF_TimersAndConstants__root_Format_list : RLF_TimersAndConstants__root_Format_Type :=
  (RLF_TimersAndConstants__t310__Format, (RLF_TimersAndConstants__n310__Format, (RLF_TimersAndConstants__n311__Format, unit_format))).

Definition RLF_TimersAndConstants__ext_Format_Type := Eval cbn in get_formats RLF_TimersAndConstants__ext_list.
Definition RLF_TimersAndConstants__ext_Format_list : RLF_TimersAndConstants__ext_Format_Type :=
  (RLF_TimersAndConstants__ext0__Format, unit__Format).

Definition RLF_TimersAndConstants__list_type : Set := (seq_type RLF_TimersAndConstants__root_list) * (seq_ext_type RLF_TimersAndConstants__ext_list).
Definition RLF_TimersAndConstants__list_cond (z : RLF_TimersAndConstants__list_type) : Prop :=
        (seq_cond RLF_TimersAndConstants__root_list (fst z)) /\ (seq_ext_cond RLF_TimersAndConstants__ext_list (snd z)).
Definition RLF_TimersAndConstants__list_format : T_Format RLF_TimersAndConstants__list_type RLF_TimersAndConstants__list_cond :=
 (* Eval compute in *) seq_ext_format RLF_TimersAndConstants__root_list RLF_TimersAndConstants__root_Format_list RLF_TimersAndConstants__ext_list RLF_TimersAndConstants__ext_Format_list.

Opaque RLF_TimersAndConstants__list_format.
Definition RLF_TimersAndConstants__F1 (z : RLF_TimersAndConstants__Type) : RLF_TimersAndConstants__list_type :=
  (((RLF_TimersAndConstants__t310 z, (RLF_TimersAndConstants__n310 z, (RLF_TimersAndConstants__n311 z, tt)))), (
(RLF_TimersAndConstants__ext0 z, tt))).
Definition RLF_TimersAndConstants__F2 (y : RLF_TimersAndConstants__list_type) : RLF_TimersAndConstants__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__RLF_TimersAndConstants__Type j0 j1 j2 i0
  end.
Definition RLF_TimersAndConstants__helper1 : (forall a : RLF_TimersAndConstants__Type, RLF_TimersAndConstants__cond a -> RLF_TimersAndConstants__list_cond (RLF_TimersAndConstants__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RLF_TimersAndConstants__helper2 : (forall a : RLF_TimersAndConstants__Type, RLF_TimersAndConstants__F2 (RLF_TimersAndConstants__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RLF_TimersAndConstants__helper3 : (forall b : RLF_TimersAndConstants__list_type, RLF_TimersAndConstants__list_cond b -> RLF_TimersAndConstants__cond (RLF_TimersAndConstants__F2 b) /\ RLF_TimersAndConstants__F1 (RLF_TimersAndConstants__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RLF_TimersAndConstants__cond, RLF_TimersAndConstants__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RLF_TimersAndConstants__Format : T_Format RLF_TimersAndConstants__Type RLF_TimersAndConstants__cond :=
 proj2_format RLF_TimersAndConstants__cond RLF_TimersAndConstants__list_format  RLF_TimersAndConstants__F1 RLF_TimersAndConstants__F2 RLF_TimersAndConstants__helper1 RLF_TimersAndConstants__helper2 RLF_TimersAndConstants__helper3.

Opaque RLF_TimersAndConstants__cond RLF_TimersAndConstants__Format.

