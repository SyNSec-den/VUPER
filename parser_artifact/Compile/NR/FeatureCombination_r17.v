Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FeatureCombination_r17__redCap_r17__Type : Set :=
 | FeatureCombination_r17__redCap_r17__true
.
Definition FeatureCombination_r17__redCap_r17__cond := (fun (_ : FeatureCombination_r17__redCap_r17__Type) => True).
Lemma FeatureCombination_r17__redCap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombination_r17__redCap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureCombination_r17__redCap_r17__nat__helper.

Definition FeatureCombination_r17__redCap_r17__F1 t :=
  match t with
  | FeatureCombination_r17__redCap_r17__true => 0
  end.
Definition FeatureCombination_r17__redCap_r17__F2 n :=
  match n with
  | 0 => FeatureCombination_r17__redCap_r17__true
  | _ => FeatureCombination_r17__redCap_r17__true
  end.
Lemma FeatureCombination_r17__redCap_r17__F1F2 : forall x : FeatureCombination_r17__redCap_r17__Type, (FeatureCombination_r17__redCap_r17__F1 x <= 0) /\ FeatureCombination_r17__redCap_r17__F2 (FeatureCombination_r17__redCap_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombination_r17__redCap_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureCombination_r17__redCap_r17__F1 (FeatureCombination_r17__redCap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureCombination_r17__smallData_r17__Type : Set :=
 | FeatureCombination_r17__smallData_r17__true
.
Definition FeatureCombination_r17__smallData_r17__cond := (fun (_ : FeatureCombination_r17__smallData_r17__Type) => True).
Lemma FeatureCombination_r17__smallData_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombination_r17__smallData_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureCombination_r17__smallData_r17__nat__helper.

Definition FeatureCombination_r17__smallData_r17__F1 t :=
  match t with
  | FeatureCombination_r17__smallData_r17__true => 0
  end.
Definition FeatureCombination_r17__smallData_r17__F2 n :=
  match n with
  | 0 => FeatureCombination_r17__smallData_r17__true
  | _ => FeatureCombination_r17__smallData_r17__true
  end.
Lemma FeatureCombination_r17__smallData_r17__F1F2 : forall x : FeatureCombination_r17__smallData_r17__Type, (FeatureCombination_r17__smallData_r17__F1 x <= 0) /\ FeatureCombination_r17__smallData_r17__F2 (FeatureCombination_r17__smallData_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombination_r17__smallData_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureCombination_r17__smallData_r17__F1 (FeatureCombination_r17__smallData_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.NSAG_List_r17.

Opaque NSAG_List_r17__cond NSAG_List_r17__Format.

Inductive FeatureCombination_r17__msg3_Repetitions_r17__Type : Set :=
 | FeatureCombination_r17__msg3_Repetitions_r17__true
.
Definition FeatureCombination_r17__msg3_Repetitions_r17__cond := (fun (_ : FeatureCombination_r17__msg3_Repetitions_r17__Type) => True).
Lemma FeatureCombination_r17__msg3_Repetitions_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombination_r17__msg3_Repetitions_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureCombination_r17__msg3_Repetitions_r17__nat__helper.

Definition FeatureCombination_r17__msg3_Repetitions_r17__F1 t :=
  match t with
  | FeatureCombination_r17__msg3_Repetitions_r17__true => 0
  end.
Definition FeatureCombination_r17__msg3_Repetitions_r17__F2 n :=
  match n with
  | 0 => FeatureCombination_r17__msg3_Repetitions_r17__true
  | _ => FeatureCombination_r17__msg3_Repetitions_r17__true
  end.
Lemma FeatureCombination_r17__msg3_Repetitions_r17__F1F2 : forall x : FeatureCombination_r17__msg3_Repetitions_r17__Type, (FeatureCombination_r17__msg3_Repetitions_r17__F1 x <= 0) /\ FeatureCombination_r17__msg3_Repetitions_r17__F2 (FeatureCombination_r17__msg3_Repetitions_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombination_r17__msg3_Repetitions_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureCombination_r17__msg3_Repetitions_r17__F1 (FeatureCombination_r17__msg3_Repetitions_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureCombination_r17__spare4__Type : Set :=
 | FeatureCombination_r17__spare4__true
.
Definition FeatureCombination_r17__spare4__cond := (fun (_ : FeatureCombination_r17__spare4__Type) => True).
Lemma FeatureCombination_r17__spare4__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombination_r17__spare4__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureCombination_r17__spare4__nat__helper.

Definition FeatureCombination_r17__spare4__F1 t :=
  match t with
  | FeatureCombination_r17__spare4__true => 0
  end.
Definition FeatureCombination_r17__spare4__F2 n :=
  match n with
  | 0 => FeatureCombination_r17__spare4__true
  | _ => FeatureCombination_r17__spare4__true
  end.
Lemma FeatureCombination_r17__spare4__F1F2 : forall x : FeatureCombination_r17__spare4__Type, (FeatureCombination_r17__spare4__F1 x <= 0) /\ FeatureCombination_r17__spare4__F2 (FeatureCombination_r17__spare4__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombination_r17__spare4__F2F1 : forall (y : nat) (H : y <= 0), FeatureCombination_r17__spare4__F1 (FeatureCombination_r17__spare4__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureCombination_r17__spare3__Type : Set :=
 | FeatureCombination_r17__spare3__true
.
Definition FeatureCombination_r17__spare3__cond := (fun (_ : FeatureCombination_r17__spare3__Type) => True).
Lemma FeatureCombination_r17__spare3__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombination_r17__spare3__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureCombination_r17__spare3__nat__helper.

Definition FeatureCombination_r17__spare3__F1 t :=
  match t with
  | FeatureCombination_r17__spare3__true => 0
  end.
Definition FeatureCombination_r17__spare3__F2 n :=
  match n with
  | 0 => FeatureCombination_r17__spare3__true
  | _ => FeatureCombination_r17__spare3__true
  end.
Lemma FeatureCombination_r17__spare3__F1F2 : forall x : FeatureCombination_r17__spare3__Type, (FeatureCombination_r17__spare3__F1 x <= 0) /\ FeatureCombination_r17__spare3__F2 (FeatureCombination_r17__spare3__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombination_r17__spare3__F2F1 : forall (y : nat) (H : y <= 0), FeatureCombination_r17__spare3__F1 (FeatureCombination_r17__spare3__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureCombination_r17__spare2__Type : Set :=
 | FeatureCombination_r17__spare2__true
.
Definition FeatureCombination_r17__spare2__cond := (fun (_ : FeatureCombination_r17__spare2__Type) => True).
Lemma FeatureCombination_r17__spare2__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombination_r17__spare2__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureCombination_r17__spare2__nat__helper.

Definition FeatureCombination_r17__spare2__F1 t :=
  match t with
  | FeatureCombination_r17__spare2__true => 0
  end.
Definition FeatureCombination_r17__spare2__F2 n :=
  match n with
  | 0 => FeatureCombination_r17__spare2__true
  | _ => FeatureCombination_r17__spare2__true
  end.
Lemma FeatureCombination_r17__spare2__F1F2 : forall x : FeatureCombination_r17__spare2__Type, (FeatureCombination_r17__spare2__F1 x <= 0) /\ FeatureCombination_r17__spare2__F2 (FeatureCombination_r17__spare2__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombination_r17__spare2__F2F1 : forall (y : nat) (H : y <= 0), FeatureCombination_r17__spare2__F1 (FeatureCombination_r17__spare2__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureCombination_r17__spare1__Type : Set :=
 | FeatureCombination_r17__spare1__true
.
Definition FeatureCombination_r17__spare1__cond := (fun (_ : FeatureCombination_r17__spare1__Type) => True).
Lemma FeatureCombination_r17__spare1__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombination_r17__spare1__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureCombination_r17__spare1__nat__helper.

Definition FeatureCombination_r17__spare1__F1 t :=
  match t with
  | FeatureCombination_r17__spare1__true => 0
  end.
Definition FeatureCombination_r17__spare1__F2 n :=
  match n with
  | 0 => FeatureCombination_r17__spare1__true
  | _ => FeatureCombination_r17__spare1__true
  end.
Lemma FeatureCombination_r17__spare1__F1F2 : forall x : FeatureCombination_r17__spare1__Type, (FeatureCombination_r17__spare1__F1 x <= 0) /\ FeatureCombination_r17__spare1__F2 (FeatureCombination_r17__spare1__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombination_r17__spare1__F2F1 : forall (y : nat) (H : y <= 0), FeatureCombination_r17__spare1__F1 (FeatureCombination_r17__spare1__F2 y) = y. enum_solve H y. Qed.

Record FeatureCombination_r17__Type : Set :=
  make__FeatureCombination_r17__Type {
    FeatureCombination_r17__redCap_r17 : option FeatureCombination_r17__redCap_r17__Type ;
    FeatureCombination_r17__smallData_r17 : option FeatureCombination_r17__smallData_r17__Type ;
    FeatureCombination_r17__nsag_r17 : option NSAG_List_r17__Type ;
    FeatureCombination_r17__msg3_Repetitions_r17 : option FeatureCombination_r17__msg3_Repetitions_r17__Type ;
    FeatureCombination_r17__spare4 : option FeatureCombination_r17__spare4__Type ;
    FeatureCombination_r17__spare3 : option FeatureCombination_r17__spare3__Type ;
    FeatureCombination_r17__spare2 : option FeatureCombination_r17__spare2__Type ;
    FeatureCombination_r17__spare1 : option FeatureCombination_r17__spare1__Type ;
}.
Definition FeatureCombination_r17__list := (
 Opt FeatureCombination_r17__redCap_r17__Type FeatureCombination_r17__redCap_r17__cond ::
 Opt FeatureCombination_r17__smallData_r17__Type FeatureCombination_r17__smallData_r17__cond ::
 Opt NSAG_List_r17__Type NSAG_List_r17__cond ::
 Opt FeatureCombination_r17__msg3_Repetitions_r17__Type FeatureCombination_r17__msg3_Repetitions_r17__cond ::
 Opt FeatureCombination_r17__spare4__Type FeatureCombination_r17__spare4__cond ::
 Opt FeatureCombination_r17__spare3__Type FeatureCombination_r17__spare3__cond ::
 Opt FeatureCombination_r17__spare2__Type FeatureCombination_r17__spare2__cond ::
 Opt FeatureCombination_r17__spare1__Type FeatureCombination_r17__spare1__cond ::
 nil).
Definition FeatureCombination_r17__cond z := 
  opt_cond FeatureCombination_r17__redCap_r17__cond (FeatureCombination_r17__redCap_r17 z) /\
  opt_cond FeatureCombination_r17__smallData_r17__cond (FeatureCombination_r17__smallData_r17 z) /\
  opt_cond NSAG_List_r17__cond (FeatureCombination_r17__nsag_r17 z) /\
  opt_cond FeatureCombination_r17__msg3_Repetitions_r17__cond (FeatureCombination_r17__msg3_Repetitions_r17 z) /\
  opt_cond FeatureCombination_r17__spare4__cond (FeatureCombination_r17__spare4 z) /\
  opt_cond FeatureCombination_r17__spare3__cond (FeatureCombination_r17__spare3 z) /\
  opt_cond FeatureCombination_r17__spare2__cond (FeatureCombination_r17__spare2 z) /\
  opt_cond FeatureCombination_r17__spare1__cond (FeatureCombination_r17__spare1 z) /\
  True.


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
Definition FeatureCombination_r17__redCap_r17__Format : T_Format FeatureCombination_r17__redCap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombination_r17__redCap_r17__nat__Format FeatureCombination_r17__redCap_r17__F1 FeatureCombination_r17__redCap_r17__F2 FeatureCombination_r17__redCap_r17__F1F2 FeatureCombination_r17__redCap_r17__F2F1.

Opaque FeatureCombination_r17__redCap_r17__cond FeatureCombination_r17__redCap_r17__Format.

Definition FeatureCombination_r17__smallData_r17__Format : T_Format FeatureCombination_r17__smallData_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombination_r17__smallData_r17__nat__Format FeatureCombination_r17__smallData_r17__F1 FeatureCombination_r17__smallData_r17__F2 FeatureCombination_r17__smallData_r17__F1F2 FeatureCombination_r17__smallData_r17__F2F1.

Opaque FeatureCombination_r17__smallData_r17__cond FeatureCombination_r17__smallData_r17__Format.

Definition FeatureCombination_r17__msg3_Repetitions_r17__Format : T_Format FeatureCombination_r17__msg3_Repetitions_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombination_r17__msg3_Repetitions_r17__nat__Format FeatureCombination_r17__msg3_Repetitions_r17__F1 FeatureCombination_r17__msg3_Repetitions_r17__F2 FeatureCombination_r17__msg3_Repetitions_r17__F1F2 FeatureCombination_r17__msg3_Repetitions_r17__F2F1.

Opaque FeatureCombination_r17__msg3_Repetitions_r17__cond FeatureCombination_r17__msg3_Repetitions_r17__Format.

Definition FeatureCombination_r17__spare4__Format : T_Format FeatureCombination_r17__spare4__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombination_r17__spare4__nat__Format FeatureCombination_r17__spare4__F1 FeatureCombination_r17__spare4__F2 FeatureCombination_r17__spare4__F1F2 FeatureCombination_r17__spare4__F2F1.

Opaque FeatureCombination_r17__spare4__cond FeatureCombination_r17__spare4__Format.

Definition FeatureCombination_r17__spare3__Format : T_Format FeatureCombination_r17__spare3__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombination_r17__spare3__nat__Format FeatureCombination_r17__spare3__F1 FeatureCombination_r17__spare3__F2 FeatureCombination_r17__spare3__F1F2 FeatureCombination_r17__spare3__F2F1.

Opaque FeatureCombination_r17__spare3__cond FeatureCombination_r17__spare3__Format.

Definition FeatureCombination_r17__spare2__Format : T_Format FeatureCombination_r17__spare2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombination_r17__spare2__nat__Format FeatureCombination_r17__spare2__F1 FeatureCombination_r17__spare2__F2 FeatureCombination_r17__spare2__F1F2 FeatureCombination_r17__spare2__F2F1.

Opaque FeatureCombination_r17__spare2__cond FeatureCombination_r17__spare2__Format.

Definition FeatureCombination_r17__spare1__Format : T_Format FeatureCombination_r17__spare1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombination_r17__spare1__nat__Format FeatureCombination_r17__spare1__F1 FeatureCombination_r17__spare1__F2 FeatureCombination_r17__spare1__F1F2 FeatureCombination_r17__spare1__F2F1.

Opaque FeatureCombination_r17__spare1__cond FeatureCombination_r17__spare1__Format.


Definition FeatureCombination_r17__Format_Type := Eval cbn in seq_format_prod FeatureCombination_r17__list.
Definition FeatureCombination_r17__Format_list : FeatureCombination_r17__Format_Type :=
  (FeatureCombination_r17__redCap_r17__Format, (FeatureCombination_r17__smallData_r17__Format, (NSAG_List_r17__Format, (FeatureCombination_r17__msg3_Repetitions_r17__Format, (FeatureCombination_r17__spare4__Format, (FeatureCombination_r17__spare3__Format, (FeatureCombination_r17__spare2__Format, (FeatureCombination_r17__spare1__Format, unit_format)))))))).
Definition FeatureCombination_r17__list__Format := (*Eval compute in *) seq_format FeatureCombination_r17__list FeatureCombination_r17__Format_list.
Definition FeatureCombination_r17__F1 z :=
  (FeatureCombination_r17__redCap_r17 z, (FeatureCombination_r17__smallData_r17 z, (FeatureCombination_r17__nsag_r17 z, (FeatureCombination_r17__msg3_Repetitions_r17 z, (FeatureCombination_r17__spare4 z, (FeatureCombination_r17__spare3 z, (FeatureCombination_r17__spare2 z, (FeatureCombination_r17__spare1 z, tt)))))))).
Definition FeatureCombination_r17__F2 (y : seq_type FeatureCombination_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__FeatureCombination_r17__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma FeatureCombination_r17__F1F2_cond (z : FeatureCombination_r17__Type)
  : FeatureCombination_r17__cond z ->
  (seq_cond FeatureCombination_r17__list (FeatureCombination_r17__F1 z)).
intro H. unfold FeatureCombination_r17__cond in H. simpl. auto. Qed.
Lemma FeatureCombination_r17__F1F2_cond2 (z : FeatureCombination_r17__Type)
 : FeatureCombination_r17__F2 (FeatureCombination_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureCombination_r17__F2F1_cond (y : seq_type FeatureCombination_r17__list)
  : seq_cond FeatureCombination_r17__list y ->
 (FeatureCombination_r17__cond (FeatureCombination_r17__F2 y)) /\  FeatureCombination_r17__F1 (FeatureCombination_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureCombination_r17__cond. simpl in *. auto.
 - simpl. unfold FeatureCombination_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureCombination_r17__Format : T_Format FeatureCombination_r17__Type FeatureCombination_r17__cond :=
        proj2_format  FeatureCombination_r17__cond FeatureCombination_r17__list__Format
    FeatureCombination_r17__F1 FeatureCombination_r17__F2 FeatureCombination_r17__F1F2_cond  FeatureCombination_r17__F1F2_cond2 FeatureCombination_r17__F2F1_cond.
Opaque FeatureCombination_r17__cond FeatureCombination_r17__Format.

