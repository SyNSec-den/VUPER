Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type : Set :=
 | PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__true
.
Definition PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__cond := (fun (_ : PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type) => True).
Lemma PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__nat__helper.

Definition PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F1 t :=
  match t with
  | PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__true => 0
  end.
Definition PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F2 n :=
  match n with
  | 0 => PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__true
  | _ => PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__true
  end.
Lemma PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F1F2 : forall x : PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type, (PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F1 x <= 0) /\ PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F2 (PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F1 x) = x. imp_solve. Qed.
Lemma PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F2F1 : forall (y : nat) (H : y <= 0), PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F1 (PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F2 y) = y. enum_solve H y. Qed.

Record PerRAAttemptInfo_r16__ext0O__Type : Set :=
  make__PerRAAttemptInfo_r16__ext0O__Type {
    PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17 : option PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type ;
}.
Definition PerRAAttemptInfo_r16__ext0O__list := (
 Opt PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__cond ::
 nil).
Definition PerRAAttemptInfo_r16__ext0O__cond z := 
  opt_cond PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__cond (PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17 z) /\
  True.

Definition PerRAAttemptInfo_r16__ext0__Type := PerRAAttemptInfo_r16__ext0O__Type.
Definition PerRAAttemptInfo_r16__ext0__cond := PerRAAttemptInfo_r16__ext0O__cond.

Record PerRAAttemptInfo_r16__Type : Set :=
  make__PerRAAttemptInfo_r16__Type {
    PerRAAttemptInfo_r16__contentionDetected_r16 : option bool ;
    PerRAAttemptInfo_r16__dlRSRPAboveThreshold_r16 : option bool ;
    PerRAAttemptInfo_r16__ext0 : option PerRAAttemptInfo_r16__ext0__Type ;
}.
Definition PerRAAttemptInfo_r16__root_list : list seq_elem := (
 Opt bool (fun _ => True) ::
 Opt bool (fun _ => True) ::
 nil).
Definition PerRAAttemptInfo_r16__ext_list : list typ := (
  typ_cons PerRAAttemptInfo_r16__ext0__Type PerRAAttemptInfo_r16__ext0__cond ::
  nil).
Definition PerRAAttemptInfo_r16__cond (z : PerRAAttemptInfo_r16__Type) := 
(  opt_cond (fun _ => True) (PerRAAttemptInfo_r16__contentionDetected_r16 z) /\
  opt_cond (fun _ => True) (PerRAAttemptInfo_r16__dlRSRPAboveThreshold_r16 z) /\
  True) /\ 
(  opt_cond PerRAAttemptInfo_r16__ext0__cond (PerRAAttemptInfo_r16__ext0 z) /\
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
Definition PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Format : T_Format PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__nat__Format PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F1 PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F2 PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F1F2 PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__F2F1.

Opaque PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__cond PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Format.


Definition PerRAAttemptInfo_r16__ext0O__Format_Type := Eval cbn in seq_format_prod PerRAAttemptInfo_r16__ext0O__list.
Definition PerRAAttemptInfo_r16__ext0O__Format_list : PerRAAttemptInfo_r16__ext0O__Format_Type :=
  (PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17__Format, unit_format).
Definition PerRAAttemptInfo_r16__ext0O__list__Format := (*Eval compute in *) seq_format PerRAAttemptInfo_r16__ext0O__list PerRAAttemptInfo_r16__ext0O__Format_list.
Definition PerRAAttemptInfo_r16__ext0O__F1 z :=
  (PerRAAttemptInfo_r16__ext0O__fallbackToFourStepRA_r17 z, tt).
Definition PerRAAttemptInfo_r16__ext0O__F2 (y : seq_type PerRAAttemptInfo_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PerRAAttemptInfo_r16__ext0O__Type i0
  end.
Lemma PerRAAttemptInfo_r16__ext0O__F1F2_cond (z : PerRAAttemptInfo_r16__ext0O__Type)
  : PerRAAttemptInfo_r16__ext0O__cond z ->
  (seq_cond PerRAAttemptInfo_r16__ext0O__list (PerRAAttemptInfo_r16__ext0O__F1 z)).
intro H. unfold PerRAAttemptInfo_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma PerRAAttemptInfo_r16__ext0O__F1F2_cond2 (z : PerRAAttemptInfo_r16__ext0O__Type)
 : PerRAAttemptInfo_r16__ext0O__F2 (PerRAAttemptInfo_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PerRAAttemptInfo_r16__ext0O__F2F1_cond (y : seq_type PerRAAttemptInfo_r16__ext0O__list)
  : seq_cond PerRAAttemptInfo_r16__ext0O__list y ->
 (PerRAAttemptInfo_r16__ext0O__cond (PerRAAttemptInfo_r16__ext0O__F2 y)) /\  PerRAAttemptInfo_r16__ext0O__F1 (PerRAAttemptInfo_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PerRAAttemptInfo_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold PerRAAttemptInfo_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PerRAAttemptInfo_r16__ext0O__Format : T_Format PerRAAttemptInfo_r16__ext0O__Type PerRAAttemptInfo_r16__ext0O__cond :=
        proj2_format  PerRAAttemptInfo_r16__ext0O__cond PerRAAttemptInfo_r16__ext0O__list__Format
    PerRAAttemptInfo_r16__ext0O__F1 PerRAAttemptInfo_r16__ext0O__F2 PerRAAttemptInfo_r16__ext0O__F1F2_cond  PerRAAttemptInfo_r16__ext0O__F1F2_cond2 PerRAAttemptInfo_r16__ext0O__F2F1_cond.
Opaque PerRAAttemptInfo_r16__ext0O__cond PerRAAttemptInfo_r16__ext0O__Format.

Definition PerRAAttemptInfo_r16__ext0__check_all_none (b : PerRAAttemptInfo_r16__ext0O__Type) : bool :=
match b with 
  | make__PerRAAttemptInfo_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PerRAAttemptInfo_r16__ext0__Format : T_Format PerRAAttemptInfo_r16__ext0__Type PerRAAttemptInfo_r16__ext0__cond :=
  restrict_add_format PerRAAttemptInfo_r16__ext0__check_all_none PerRAAttemptInfo_r16__ext0O__Format.

Opaque PerRAAttemptInfo_r16__ext0__cond PerRAAttemptInfo_r16__ext0__Format.


Definition PerRAAttemptInfo_r16__root_Format_Type := Eval cbn in seq_format_prod PerRAAttemptInfo_r16__root_list.
Definition PerRAAttemptInfo_r16__root_Format_list : PerRAAttemptInfo_r16__root_Format_Type :=
  (bool__Format, (bool__Format, unit_format)).

Definition PerRAAttemptInfo_r16__ext_Format_Type := Eval cbn in get_formats PerRAAttemptInfo_r16__ext_list.
Definition PerRAAttemptInfo_r16__ext_Format_list : PerRAAttemptInfo_r16__ext_Format_Type :=
  (PerRAAttemptInfo_r16__ext0__Format, unit__Format).

Definition PerRAAttemptInfo_r16__list_type : Set := (seq_type PerRAAttemptInfo_r16__root_list) * (seq_ext_type PerRAAttemptInfo_r16__ext_list).
Definition PerRAAttemptInfo_r16__list_cond (z : PerRAAttemptInfo_r16__list_type) : Prop :=
        (seq_cond PerRAAttemptInfo_r16__root_list (fst z)) /\ (seq_ext_cond PerRAAttemptInfo_r16__ext_list (snd z)).
Definition PerRAAttemptInfo_r16__list_format : T_Format PerRAAttemptInfo_r16__list_type PerRAAttemptInfo_r16__list_cond :=
 (* Eval compute in *) seq_ext_format PerRAAttemptInfo_r16__root_list PerRAAttemptInfo_r16__root_Format_list PerRAAttemptInfo_r16__ext_list PerRAAttemptInfo_r16__ext_Format_list.

Opaque PerRAAttemptInfo_r16__list_format.
Definition PerRAAttemptInfo_r16__F1 (z : PerRAAttemptInfo_r16__Type) : PerRAAttemptInfo_r16__list_type :=
  (((PerRAAttemptInfo_r16__contentionDetected_r16 z, (PerRAAttemptInfo_r16__dlRSRPAboveThreshold_r16 z, tt))), (
(PerRAAttemptInfo_r16__ext0 z, tt))).
Definition PerRAAttemptInfo_r16__F2 (y : PerRAAttemptInfo_r16__list_type) : PerRAAttemptInfo_r16__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__PerRAAttemptInfo_r16__Type j0 j1 i0
  end.
Definition PerRAAttemptInfo_r16__helper1 : (forall a : PerRAAttemptInfo_r16__Type, PerRAAttemptInfo_r16__cond a -> PerRAAttemptInfo_r16__list_cond (PerRAAttemptInfo_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PerRAAttemptInfo_r16__helper2 : (forall a : PerRAAttemptInfo_r16__Type, PerRAAttemptInfo_r16__F2 (PerRAAttemptInfo_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PerRAAttemptInfo_r16__helper3 : (forall b : PerRAAttemptInfo_r16__list_type, PerRAAttemptInfo_r16__list_cond b -> PerRAAttemptInfo_r16__cond (PerRAAttemptInfo_r16__F2 b) /\ PerRAAttemptInfo_r16__F1 (PerRAAttemptInfo_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PerRAAttemptInfo_r16__cond, PerRAAttemptInfo_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PerRAAttemptInfo_r16__Format : T_Format PerRAAttemptInfo_r16__Type PerRAAttemptInfo_r16__cond :=
 proj2_format PerRAAttemptInfo_r16__cond PerRAAttemptInfo_r16__list_format  PerRAAttemptInfo_r16__F1 PerRAAttemptInfo_r16__F2 PerRAAttemptInfo_r16__helper1 PerRAAttemptInfo_r16__helper2 PerRAAttemptInfo_r16__helper3.

Opaque PerRAAttemptInfo_r16__cond PerRAAttemptInfo_r16__Format.

