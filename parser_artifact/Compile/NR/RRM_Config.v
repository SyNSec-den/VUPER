Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Inductive RRM_Config__ue_InactiveTime__Type : Set :=
 | RRM_Config__ue_InactiveTime__s1
 | RRM_Config__ue_InactiveTime__s2
 | RRM_Config__ue_InactiveTime__s3
 | RRM_Config__ue_InactiveTime__s5
 | RRM_Config__ue_InactiveTime__s7
 | RRM_Config__ue_InactiveTime__s10
 | RRM_Config__ue_InactiveTime__s15
 | RRM_Config__ue_InactiveTime__s20
 | RRM_Config__ue_InactiveTime__s25
 | RRM_Config__ue_InactiveTime__s30
 | RRM_Config__ue_InactiveTime__s40
 | RRM_Config__ue_InactiveTime__s50
 | RRM_Config__ue_InactiveTime__min1
 | RRM_Config__ue_InactiveTime__min1s20
 | RRM_Config__ue_InactiveTime__min1s40
 | RRM_Config__ue_InactiveTime__min2
 | RRM_Config__ue_InactiveTime__min2s30
 | RRM_Config__ue_InactiveTime__min3
 | RRM_Config__ue_InactiveTime__min3s30
 | RRM_Config__ue_InactiveTime__min4
 | RRM_Config__ue_InactiveTime__min5
 | RRM_Config__ue_InactiveTime__min6
 | RRM_Config__ue_InactiveTime__min7
 | RRM_Config__ue_InactiveTime__min8
 | RRM_Config__ue_InactiveTime__min9
 | RRM_Config__ue_InactiveTime__min10
 | RRM_Config__ue_InactiveTime__min12
 | RRM_Config__ue_InactiveTime__min14
 | RRM_Config__ue_InactiveTime__min17
 | RRM_Config__ue_InactiveTime__min20
 | RRM_Config__ue_InactiveTime__min24
 | RRM_Config__ue_InactiveTime__min28
 | RRM_Config__ue_InactiveTime__min33
 | RRM_Config__ue_InactiveTime__min38
 | RRM_Config__ue_InactiveTime__min44
 | RRM_Config__ue_InactiveTime__min50
 | RRM_Config__ue_InactiveTime__hr1
 | RRM_Config__ue_InactiveTime__hr1min30
 | RRM_Config__ue_InactiveTime__hr2
 | RRM_Config__ue_InactiveTime__hr2min30
 | RRM_Config__ue_InactiveTime__hr3
 | RRM_Config__ue_InactiveTime__hr3min30
 | RRM_Config__ue_InactiveTime__hr4
 | RRM_Config__ue_InactiveTime__hr5
 | RRM_Config__ue_InactiveTime__hr6
 | RRM_Config__ue_InactiveTime__hr8
 | RRM_Config__ue_InactiveTime__hr10
 | RRM_Config__ue_InactiveTime__hr13
 | RRM_Config__ue_InactiveTime__hr16
 | RRM_Config__ue_InactiveTime__hr20
 | RRM_Config__ue_InactiveTime__day1
 | RRM_Config__ue_InactiveTime__day1hr12
 | RRM_Config__ue_InactiveTime__day2
 | RRM_Config__ue_InactiveTime__day2hr12
 | RRM_Config__ue_InactiveTime__day3
 | RRM_Config__ue_InactiveTime__day4
 | RRM_Config__ue_InactiveTime__day5
 | RRM_Config__ue_InactiveTime__day7
 | RRM_Config__ue_InactiveTime__day10
 | RRM_Config__ue_InactiveTime__day14
 | RRM_Config__ue_InactiveTime__day19
 | RRM_Config__ue_InactiveTime__day24
 | RRM_Config__ue_InactiveTime__day30
 | RRM_Config__ue_InactiveTime__dayMoreThan30
.
Definition RRM_Config__ue_InactiveTime__cond := (fun (_ : RRM_Config__ue_InactiveTime__Type) => True).
Lemma RRM_Config__ue_InactiveTime__nat__helper : to_bit_sz 63 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRM_Config__ue_InactiveTime__nat__Format : T_Format nat (fun z => (z <= 63)) :=
  nat_enum_format 63 RRM_Config__ue_InactiveTime__nat__helper.

Definition RRM_Config__ue_InactiveTime__F1 t :=
  match t with
  | RRM_Config__ue_InactiveTime__s1 => 0
  | RRM_Config__ue_InactiveTime__s2 => 1
  | RRM_Config__ue_InactiveTime__s3 => 2
  | RRM_Config__ue_InactiveTime__s5 => 3
  | RRM_Config__ue_InactiveTime__s7 => 4
  | RRM_Config__ue_InactiveTime__s10 => 5
  | RRM_Config__ue_InactiveTime__s15 => 6
  | RRM_Config__ue_InactiveTime__s20 => 7
  | RRM_Config__ue_InactiveTime__s25 => 8
  | RRM_Config__ue_InactiveTime__s30 => 9
  | RRM_Config__ue_InactiveTime__s40 => 10
  | RRM_Config__ue_InactiveTime__s50 => 11
  | RRM_Config__ue_InactiveTime__min1 => 12
  | RRM_Config__ue_InactiveTime__min1s20 => 13
  | RRM_Config__ue_InactiveTime__min1s40 => 14
  | RRM_Config__ue_InactiveTime__min2 => 15
  | RRM_Config__ue_InactiveTime__min2s30 => 16
  | RRM_Config__ue_InactiveTime__min3 => 17
  | RRM_Config__ue_InactiveTime__min3s30 => 18
  | RRM_Config__ue_InactiveTime__min4 => 19
  | RRM_Config__ue_InactiveTime__min5 => 20
  | RRM_Config__ue_InactiveTime__min6 => 21
  | RRM_Config__ue_InactiveTime__min7 => 22
  | RRM_Config__ue_InactiveTime__min8 => 23
  | RRM_Config__ue_InactiveTime__min9 => 24
  | RRM_Config__ue_InactiveTime__min10 => 25
  | RRM_Config__ue_InactiveTime__min12 => 26
  | RRM_Config__ue_InactiveTime__min14 => 27
  | RRM_Config__ue_InactiveTime__min17 => 28
  | RRM_Config__ue_InactiveTime__min20 => 29
  | RRM_Config__ue_InactiveTime__min24 => 30
  | RRM_Config__ue_InactiveTime__min28 => 31
  | RRM_Config__ue_InactiveTime__min33 => 32
  | RRM_Config__ue_InactiveTime__min38 => 33
  | RRM_Config__ue_InactiveTime__min44 => 34
  | RRM_Config__ue_InactiveTime__min50 => 35
  | RRM_Config__ue_InactiveTime__hr1 => 36
  | RRM_Config__ue_InactiveTime__hr1min30 => 37
  | RRM_Config__ue_InactiveTime__hr2 => 38
  | RRM_Config__ue_InactiveTime__hr2min30 => 39
  | RRM_Config__ue_InactiveTime__hr3 => 40
  | RRM_Config__ue_InactiveTime__hr3min30 => 41
  | RRM_Config__ue_InactiveTime__hr4 => 42
  | RRM_Config__ue_InactiveTime__hr5 => 43
  | RRM_Config__ue_InactiveTime__hr6 => 44
  | RRM_Config__ue_InactiveTime__hr8 => 45
  | RRM_Config__ue_InactiveTime__hr10 => 46
  | RRM_Config__ue_InactiveTime__hr13 => 47
  | RRM_Config__ue_InactiveTime__hr16 => 48
  | RRM_Config__ue_InactiveTime__hr20 => 49
  | RRM_Config__ue_InactiveTime__day1 => 50
  | RRM_Config__ue_InactiveTime__day1hr12 => 51
  | RRM_Config__ue_InactiveTime__day2 => 52
  | RRM_Config__ue_InactiveTime__day2hr12 => 53
  | RRM_Config__ue_InactiveTime__day3 => 54
  | RRM_Config__ue_InactiveTime__day4 => 55
  | RRM_Config__ue_InactiveTime__day5 => 56
  | RRM_Config__ue_InactiveTime__day7 => 57
  | RRM_Config__ue_InactiveTime__day10 => 58
  | RRM_Config__ue_InactiveTime__day14 => 59
  | RRM_Config__ue_InactiveTime__day19 => 60
  | RRM_Config__ue_InactiveTime__day24 => 61
  | RRM_Config__ue_InactiveTime__day30 => 62
  | RRM_Config__ue_InactiveTime__dayMoreThan30 => 63
  end.
Definition RRM_Config__ue_InactiveTime__F2 n :=
  match n with
  | 0 => RRM_Config__ue_InactiveTime__s1
  | 1 => RRM_Config__ue_InactiveTime__s2
  | 2 => RRM_Config__ue_InactiveTime__s3
  | 3 => RRM_Config__ue_InactiveTime__s5
  | 4 => RRM_Config__ue_InactiveTime__s7
  | 5 => RRM_Config__ue_InactiveTime__s10
  | 6 => RRM_Config__ue_InactiveTime__s15
  | 7 => RRM_Config__ue_InactiveTime__s20
  | 8 => RRM_Config__ue_InactiveTime__s25
  | 9 => RRM_Config__ue_InactiveTime__s30
  | 10 => RRM_Config__ue_InactiveTime__s40
  | 11 => RRM_Config__ue_InactiveTime__s50
  | 12 => RRM_Config__ue_InactiveTime__min1
  | 13 => RRM_Config__ue_InactiveTime__min1s20
  | 14 => RRM_Config__ue_InactiveTime__min1s40
  | 15 => RRM_Config__ue_InactiveTime__min2
  | 16 => RRM_Config__ue_InactiveTime__min2s30
  | 17 => RRM_Config__ue_InactiveTime__min3
  | 18 => RRM_Config__ue_InactiveTime__min3s30
  | 19 => RRM_Config__ue_InactiveTime__min4
  | 20 => RRM_Config__ue_InactiveTime__min5
  | 21 => RRM_Config__ue_InactiveTime__min6
  | 22 => RRM_Config__ue_InactiveTime__min7
  | 23 => RRM_Config__ue_InactiveTime__min8
  | 24 => RRM_Config__ue_InactiveTime__min9
  | 25 => RRM_Config__ue_InactiveTime__min10
  | 26 => RRM_Config__ue_InactiveTime__min12
  | 27 => RRM_Config__ue_InactiveTime__min14
  | 28 => RRM_Config__ue_InactiveTime__min17
  | 29 => RRM_Config__ue_InactiveTime__min20
  | 30 => RRM_Config__ue_InactiveTime__min24
  | 31 => RRM_Config__ue_InactiveTime__min28
  | 32 => RRM_Config__ue_InactiveTime__min33
  | 33 => RRM_Config__ue_InactiveTime__min38
  | 34 => RRM_Config__ue_InactiveTime__min44
  | 35 => RRM_Config__ue_InactiveTime__min50
  | 36 => RRM_Config__ue_InactiveTime__hr1
  | 37 => RRM_Config__ue_InactiveTime__hr1min30
  | 38 => RRM_Config__ue_InactiveTime__hr2
  | 39 => RRM_Config__ue_InactiveTime__hr2min30
  | 40 => RRM_Config__ue_InactiveTime__hr3
  | 41 => RRM_Config__ue_InactiveTime__hr3min30
  | 42 => RRM_Config__ue_InactiveTime__hr4
  | 43 => RRM_Config__ue_InactiveTime__hr5
  | 44 => RRM_Config__ue_InactiveTime__hr6
  | 45 => RRM_Config__ue_InactiveTime__hr8
  | 46 => RRM_Config__ue_InactiveTime__hr10
  | 47 => RRM_Config__ue_InactiveTime__hr13
  | 48 => RRM_Config__ue_InactiveTime__hr16
  | 49 => RRM_Config__ue_InactiveTime__hr20
  | 50 => RRM_Config__ue_InactiveTime__day1
  | 51 => RRM_Config__ue_InactiveTime__day1hr12
  | 52 => RRM_Config__ue_InactiveTime__day2
  | 53 => RRM_Config__ue_InactiveTime__day2hr12
  | 54 => RRM_Config__ue_InactiveTime__day3
  | 55 => RRM_Config__ue_InactiveTime__day4
  | 56 => RRM_Config__ue_InactiveTime__day5
  | 57 => RRM_Config__ue_InactiveTime__day7
  | 58 => RRM_Config__ue_InactiveTime__day10
  | 59 => RRM_Config__ue_InactiveTime__day14
  | 60 => RRM_Config__ue_InactiveTime__day19
  | 61 => RRM_Config__ue_InactiveTime__day24
  | 62 => RRM_Config__ue_InactiveTime__day30
  | 63 => RRM_Config__ue_InactiveTime__dayMoreThan30
  | _ => RRM_Config__ue_InactiveTime__s1
  end.
Lemma RRM_Config__ue_InactiveTime__F1F2 : forall x : RRM_Config__ue_InactiveTime__Type, (RRM_Config__ue_InactiveTime__F1 x <= 63) /\ RRM_Config__ue_InactiveTime__F2 (RRM_Config__ue_InactiveTime__F1 x) = x. imp_solve. Qed.
Lemma RRM_Config__ue_InactiveTime__F2F1 : forall (y : nat) (H : y <= 63), RRM_Config__ue_InactiveTime__F1 (RRM_Config__ue_InactiveTime__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasResultList2NR.

Opaque MeasResultList2NR__cond MeasResultList2NR__Format.

Require Import NR.MeasResultServFreqListEUTRA_SCG.

Opaque MeasResultServFreqListEUTRA_SCG__cond MeasResultServFreqListEUTRA_SCG__Format.

Record RRM_Config__ext0O__Type : Set :=
  make__RRM_Config__ext0O__Type {
    RRM_Config__ext0O__candidateCellInfoListSN_EUTRA : option MeasResultServFreqListEUTRA_SCG__Type ;
}.
Definition RRM_Config__ext0O__list := (
 Opt MeasResultServFreqListEUTRA_SCG__Type MeasResultServFreqListEUTRA_SCG__cond ::
 nil).
Definition RRM_Config__ext0O__cond z := 
  opt_cond MeasResultServFreqListEUTRA_SCG__cond (RRM_Config__ext0O__candidateCellInfoListSN_EUTRA z) /\
  True.

Definition RRM_Config__ext0__Type := RRM_Config__ext0O__Type.
Definition RRM_Config__ext0__cond := RRM_Config__ext0O__cond.

Record RRM_Config__Type : Set :=
  make__RRM_Config__Type {
    RRM_Config__ue_InactiveTime : option RRM_Config__ue_InactiveTime__Type ;
    RRM_Config__candidateCellInfoList : option MeasResultList2NR__Type ;
    RRM_Config__ext0 : option RRM_Config__ext0__Type ;
}.
Definition RRM_Config__root_list : list seq_elem := (
 Opt RRM_Config__ue_InactiveTime__Type RRM_Config__ue_InactiveTime__cond ::
 Opt MeasResultList2NR__Type MeasResultList2NR__cond ::
 nil).
Definition RRM_Config__ext_list : list typ := (
  typ_cons RRM_Config__ext0__Type RRM_Config__ext0__cond ::
  nil).
Definition RRM_Config__cond (z : RRM_Config__Type) := 
(  opt_cond RRM_Config__ue_InactiveTime__cond (RRM_Config__ue_InactiveTime z) /\
  opt_cond MeasResultList2NR__cond (RRM_Config__candidateCellInfoList z) /\
  True) /\ 
(  opt_cond RRM_Config__ext0__cond (RRM_Config__ext0 z) /\
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
Definition RRM_Config__ue_InactiveTime__Format : T_Format RRM_Config__ue_InactiveTime__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRM_Config__ue_InactiveTime__nat__Format RRM_Config__ue_InactiveTime__F1 RRM_Config__ue_InactiveTime__F2 RRM_Config__ue_InactiveTime__F1F2 RRM_Config__ue_InactiveTime__F2F1.

Opaque RRM_Config__ue_InactiveTime__cond RRM_Config__ue_InactiveTime__Format.


Definition RRM_Config__ext0O__Format_Type := Eval cbn in seq_format_prod RRM_Config__ext0O__list.
Definition RRM_Config__ext0O__Format_list : RRM_Config__ext0O__Format_Type :=
  (MeasResultServFreqListEUTRA_SCG__Format, unit_format).
Definition RRM_Config__ext0O__list__Format := (*Eval compute in *) seq_format RRM_Config__ext0O__list RRM_Config__ext0O__Format_list.
Definition RRM_Config__ext0O__F1 z :=
  (RRM_Config__ext0O__candidateCellInfoListSN_EUTRA z, tt).
Definition RRM_Config__ext0O__F2 (y : seq_type RRM_Config__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RRM_Config__ext0O__Type i0
  end.
Lemma RRM_Config__ext0O__F1F2_cond (z : RRM_Config__ext0O__Type)
  : RRM_Config__ext0O__cond z ->
  (seq_cond RRM_Config__ext0O__list (RRM_Config__ext0O__F1 z)).
intro H. unfold RRM_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma RRM_Config__ext0O__F1F2_cond2 (z : RRM_Config__ext0O__Type)
 : RRM_Config__ext0O__F2 (RRM_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRM_Config__ext0O__F2F1_cond (y : seq_type RRM_Config__ext0O__list)
  : seq_cond RRM_Config__ext0O__list y ->
 (RRM_Config__ext0O__cond (RRM_Config__ext0O__F2 y)) /\  RRM_Config__ext0O__F1 (RRM_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRM_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold RRM_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRM_Config__ext0O__Format : T_Format RRM_Config__ext0O__Type RRM_Config__ext0O__cond :=
        proj2_format  RRM_Config__ext0O__cond RRM_Config__ext0O__list__Format
    RRM_Config__ext0O__F1 RRM_Config__ext0O__F2 RRM_Config__ext0O__F1F2_cond  RRM_Config__ext0O__F1F2_cond2 RRM_Config__ext0O__F2F1_cond.
Opaque RRM_Config__ext0O__cond RRM_Config__ext0O__Format.

Definition RRM_Config__ext0__check_all_none (b : RRM_Config__ext0O__Type) : bool :=
match b with 
  | make__RRM_Config__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RRM_Config__ext0__Format : T_Format RRM_Config__ext0__Type RRM_Config__ext0__cond :=
  restrict_add_format RRM_Config__ext0__check_all_none RRM_Config__ext0O__Format.

Opaque RRM_Config__ext0__cond RRM_Config__ext0__Format.


Definition RRM_Config__root_Format_Type := Eval cbn in seq_format_prod RRM_Config__root_list.
Definition RRM_Config__root_Format_list : RRM_Config__root_Format_Type :=
  (RRM_Config__ue_InactiveTime__Format, (MeasResultList2NR__Format, unit_format)).

Definition RRM_Config__ext_Format_Type := Eval cbn in get_formats RRM_Config__ext_list.
Definition RRM_Config__ext_Format_list : RRM_Config__ext_Format_Type :=
  (RRM_Config__ext0__Format, unit__Format).

Definition RRM_Config__list_type : Set := (seq_type RRM_Config__root_list) * (seq_ext_type RRM_Config__ext_list).
Definition RRM_Config__list_cond (z : RRM_Config__list_type) : Prop :=
        (seq_cond RRM_Config__root_list (fst z)) /\ (seq_ext_cond RRM_Config__ext_list (snd z)).
Definition RRM_Config__list_format : T_Format RRM_Config__list_type RRM_Config__list_cond :=
 (* Eval compute in *) seq_ext_format RRM_Config__root_list RRM_Config__root_Format_list RRM_Config__ext_list RRM_Config__ext_Format_list.

Opaque RRM_Config__list_format.
Definition RRM_Config__F1 (z : RRM_Config__Type) : RRM_Config__list_type :=
  (((RRM_Config__ue_InactiveTime z, (RRM_Config__candidateCellInfoList z, tt))), (
(RRM_Config__ext0 z, tt))).
Definition RRM_Config__F2 (y : RRM_Config__list_type) : RRM_Config__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__RRM_Config__Type j0 j1 i0
  end.
Definition RRM_Config__helper1 : (forall a : RRM_Config__Type, RRM_Config__cond a -> RRM_Config__list_cond (RRM_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RRM_Config__helper2 : (forall a : RRM_Config__Type, RRM_Config__F2 (RRM_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RRM_Config__helper3 : (forall b : RRM_Config__list_type, RRM_Config__list_cond b -> RRM_Config__cond (RRM_Config__F2 b) /\ RRM_Config__F1 (RRM_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RRM_Config__cond, RRM_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RRM_Config__Format : T_Format RRM_Config__Type RRM_Config__cond :=
 proj2_format RRM_Config__cond RRM_Config__list_format  RRM_Config__F1 RRM_Config__F2 RRM_Config__helper1 RRM_Config__helper2 RRM_Config__helper3.

Opaque RRM_Config__cond RRM_Config__Format.

