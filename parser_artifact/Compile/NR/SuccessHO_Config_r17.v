Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SuccessHO_Config_r17__thresholdPercentageT304_r17__Type : Set :=
 | SuccessHO_Config_r17__thresholdPercentageT304_r17__p40
 | SuccessHO_Config_r17__thresholdPercentageT304_r17__p60
 | SuccessHO_Config_r17__thresholdPercentageT304_r17__p80
 | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare5
 | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare4
 | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare3
 | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare2
 | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare1
.
Definition SuccessHO_Config_r17__thresholdPercentageT304_r17__cond := (fun (_ : SuccessHO_Config_r17__thresholdPercentageT304_r17__Type) => True).
Lemma SuccessHO_Config_r17__thresholdPercentageT304_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SuccessHO_Config_r17__thresholdPercentageT304_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SuccessHO_Config_r17__thresholdPercentageT304_r17__nat__helper.

Definition SuccessHO_Config_r17__thresholdPercentageT304_r17__F1 t :=
  match t with
  | SuccessHO_Config_r17__thresholdPercentageT304_r17__p40 => 0
  | SuccessHO_Config_r17__thresholdPercentageT304_r17__p60 => 1
  | SuccessHO_Config_r17__thresholdPercentageT304_r17__p80 => 2
  | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare5 => 3
  | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare4 => 4
  | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare3 => 5
  | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare2 => 6
  | SuccessHO_Config_r17__thresholdPercentageT304_r17__spare1 => 7
  end.
Definition SuccessHO_Config_r17__thresholdPercentageT304_r17__F2 n :=
  match n with
  | 0 => SuccessHO_Config_r17__thresholdPercentageT304_r17__p40
  | 1 => SuccessHO_Config_r17__thresholdPercentageT304_r17__p60
  | 2 => SuccessHO_Config_r17__thresholdPercentageT304_r17__p80
  | 3 => SuccessHO_Config_r17__thresholdPercentageT304_r17__spare5
  | 4 => SuccessHO_Config_r17__thresholdPercentageT304_r17__spare4
  | 5 => SuccessHO_Config_r17__thresholdPercentageT304_r17__spare3
  | 6 => SuccessHO_Config_r17__thresholdPercentageT304_r17__spare2
  | 7 => SuccessHO_Config_r17__thresholdPercentageT304_r17__spare1
  | _ => SuccessHO_Config_r17__thresholdPercentageT304_r17__p40
  end.
Lemma SuccessHO_Config_r17__thresholdPercentageT304_r17__F1F2 : forall x : SuccessHO_Config_r17__thresholdPercentageT304_r17__Type, (SuccessHO_Config_r17__thresholdPercentageT304_r17__F1 x <= 7) /\ SuccessHO_Config_r17__thresholdPercentageT304_r17__F2 (SuccessHO_Config_r17__thresholdPercentageT304_r17__F1 x) = x. imp_solve. Qed.
Lemma SuccessHO_Config_r17__thresholdPercentageT304_r17__F2F1 : forall (y : nat) (H : y <= 7), SuccessHO_Config_r17__thresholdPercentageT304_r17__F1 (SuccessHO_Config_r17__thresholdPercentageT304_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SuccessHO_Config_r17__thresholdPercentageT310_r17__Type : Set :=
 | SuccessHO_Config_r17__thresholdPercentageT310_r17__p40
 | SuccessHO_Config_r17__thresholdPercentageT310_r17__p60
 | SuccessHO_Config_r17__thresholdPercentageT310_r17__p80
 | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare5
 | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare4
 | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare3
 | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare2
 | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare1
.
Definition SuccessHO_Config_r17__thresholdPercentageT310_r17__cond := (fun (_ : SuccessHO_Config_r17__thresholdPercentageT310_r17__Type) => True).
Lemma SuccessHO_Config_r17__thresholdPercentageT310_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SuccessHO_Config_r17__thresholdPercentageT310_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SuccessHO_Config_r17__thresholdPercentageT310_r17__nat__helper.

Definition SuccessHO_Config_r17__thresholdPercentageT310_r17__F1 t :=
  match t with
  | SuccessHO_Config_r17__thresholdPercentageT310_r17__p40 => 0
  | SuccessHO_Config_r17__thresholdPercentageT310_r17__p60 => 1
  | SuccessHO_Config_r17__thresholdPercentageT310_r17__p80 => 2
  | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare5 => 3
  | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare4 => 4
  | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare3 => 5
  | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare2 => 6
  | SuccessHO_Config_r17__thresholdPercentageT310_r17__spare1 => 7
  end.
Definition SuccessHO_Config_r17__thresholdPercentageT310_r17__F2 n :=
  match n with
  | 0 => SuccessHO_Config_r17__thresholdPercentageT310_r17__p40
  | 1 => SuccessHO_Config_r17__thresholdPercentageT310_r17__p60
  | 2 => SuccessHO_Config_r17__thresholdPercentageT310_r17__p80
  | 3 => SuccessHO_Config_r17__thresholdPercentageT310_r17__spare5
  | 4 => SuccessHO_Config_r17__thresholdPercentageT310_r17__spare4
  | 5 => SuccessHO_Config_r17__thresholdPercentageT310_r17__spare3
  | 6 => SuccessHO_Config_r17__thresholdPercentageT310_r17__spare2
  | 7 => SuccessHO_Config_r17__thresholdPercentageT310_r17__spare1
  | _ => SuccessHO_Config_r17__thresholdPercentageT310_r17__p40
  end.
Lemma SuccessHO_Config_r17__thresholdPercentageT310_r17__F1F2 : forall x : SuccessHO_Config_r17__thresholdPercentageT310_r17__Type, (SuccessHO_Config_r17__thresholdPercentageT310_r17__F1 x <= 7) /\ SuccessHO_Config_r17__thresholdPercentageT310_r17__F2 (SuccessHO_Config_r17__thresholdPercentageT310_r17__F1 x) = x. imp_solve. Qed.
Lemma SuccessHO_Config_r17__thresholdPercentageT310_r17__F2F1 : forall (y : nat) (H : y <= 7), SuccessHO_Config_r17__thresholdPercentageT310_r17__F1 (SuccessHO_Config_r17__thresholdPercentageT310_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SuccessHO_Config_r17__thresholdPercentageT312_r17__Type : Set :=
 | SuccessHO_Config_r17__thresholdPercentageT312_r17__p20
 | SuccessHO_Config_r17__thresholdPercentageT312_r17__p40
 | SuccessHO_Config_r17__thresholdPercentageT312_r17__p60
 | SuccessHO_Config_r17__thresholdPercentageT312_r17__p80
 | SuccessHO_Config_r17__thresholdPercentageT312_r17__spare4
 | SuccessHO_Config_r17__thresholdPercentageT312_r17__spare3
 | SuccessHO_Config_r17__thresholdPercentageT312_r17__spare2
 | SuccessHO_Config_r17__thresholdPercentageT312_r17__spare1
.
Definition SuccessHO_Config_r17__thresholdPercentageT312_r17__cond := (fun (_ : SuccessHO_Config_r17__thresholdPercentageT312_r17__Type) => True).
Lemma SuccessHO_Config_r17__thresholdPercentageT312_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SuccessHO_Config_r17__thresholdPercentageT312_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SuccessHO_Config_r17__thresholdPercentageT312_r17__nat__helper.

Definition SuccessHO_Config_r17__thresholdPercentageT312_r17__F1 t :=
  match t with
  | SuccessHO_Config_r17__thresholdPercentageT312_r17__p20 => 0
  | SuccessHO_Config_r17__thresholdPercentageT312_r17__p40 => 1
  | SuccessHO_Config_r17__thresholdPercentageT312_r17__p60 => 2
  | SuccessHO_Config_r17__thresholdPercentageT312_r17__p80 => 3
  | SuccessHO_Config_r17__thresholdPercentageT312_r17__spare4 => 4
  | SuccessHO_Config_r17__thresholdPercentageT312_r17__spare3 => 5
  | SuccessHO_Config_r17__thresholdPercentageT312_r17__spare2 => 6
  | SuccessHO_Config_r17__thresholdPercentageT312_r17__spare1 => 7
  end.
Definition SuccessHO_Config_r17__thresholdPercentageT312_r17__F2 n :=
  match n with
  | 0 => SuccessHO_Config_r17__thresholdPercentageT312_r17__p20
  | 1 => SuccessHO_Config_r17__thresholdPercentageT312_r17__p40
  | 2 => SuccessHO_Config_r17__thresholdPercentageT312_r17__p60
  | 3 => SuccessHO_Config_r17__thresholdPercentageT312_r17__p80
  | 4 => SuccessHO_Config_r17__thresholdPercentageT312_r17__spare4
  | 5 => SuccessHO_Config_r17__thresholdPercentageT312_r17__spare3
  | 6 => SuccessHO_Config_r17__thresholdPercentageT312_r17__spare2
  | 7 => SuccessHO_Config_r17__thresholdPercentageT312_r17__spare1
  | _ => SuccessHO_Config_r17__thresholdPercentageT312_r17__p20
  end.
Lemma SuccessHO_Config_r17__thresholdPercentageT312_r17__F1F2 : forall x : SuccessHO_Config_r17__thresholdPercentageT312_r17__Type, (SuccessHO_Config_r17__thresholdPercentageT312_r17__F1 x <= 7) /\ SuccessHO_Config_r17__thresholdPercentageT312_r17__F2 (SuccessHO_Config_r17__thresholdPercentageT312_r17__F1 x) = x. imp_solve. Qed.
Lemma SuccessHO_Config_r17__thresholdPercentageT312_r17__F2F1 : forall (y : nat) (H : y <= 7), SuccessHO_Config_r17__thresholdPercentageT312_r17__F1 (SuccessHO_Config_r17__thresholdPercentageT312_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Type : Set :=
 | SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__true
.
Definition SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__cond := (fun (_ : SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Type) => True).
Lemma SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__nat__helper.

Definition SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F1 t :=
  match t with
  | SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__true => 0
  end.
Definition SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F2 n :=
  match n with
  | 0 => SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__true
  | _ => SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__true
  end.
Lemma SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F1F2 : forall x : SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Type, (SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F1 x <= 0) /\ SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F2 (SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F1 x) = x. imp_solve. Qed.
Lemma SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F2F1 : forall (y : nat) (H : y <= 0), SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F1 (SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F2 y) = y. enum_solve H y. Qed.

Record SuccessHO_Config_r17__Type : Set :=
  make__SuccessHO_Config_r17__Type {
    SuccessHO_Config_r17__thresholdPercentageT304_r17 : option SuccessHO_Config_r17__thresholdPercentageT304_r17__Type ;
    SuccessHO_Config_r17__thresholdPercentageT310_r17 : option SuccessHO_Config_r17__thresholdPercentageT310_r17__Type ;
    SuccessHO_Config_r17__thresholdPercentageT312_r17 : option SuccessHO_Config_r17__thresholdPercentageT312_r17__Type ;
    SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17 : option SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Type ;
}.
Definition SuccessHO_Config_r17__root_list : list seq_elem := (
 Opt SuccessHO_Config_r17__thresholdPercentageT304_r17__Type SuccessHO_Config_r17__thresholdPercentageT304_r17__cond ::
 Opt SuccessHO_Config_r17__thresholdPercentageT310_r17__Type SuccessHO_Config_r17__thresholdPercentageT310_r17__cond ::
 Opt SuccessHO_Config_r17__thresholdPercentageT312_r17__Type SuccessHO_Config_r17__thresholdPercentageT312_r17__cond ::
 Opt SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Type SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__cond ::
 nil).
Definition SuccessHO_Config_r17__ext_list : list typ := (
  nil).
Definition SuccessHO_Config_r17__cond (z : SuccessHO_Config_r17__Type) := 
(  opt_cond SuccessHO_Config_r17__thresholdPercentageT304_r17__cond (SuccessHO_Config_r17__thresholdPercentageT304_r17 z) /\
  opt_cond SuccessHO_Config_r17__thresholdPercentageT310_r17__cond (SuccessHO_Config_r17__thresholdPercentageT310_r17 z) /\
  opt_cond SuccessHO_Config_r17__thresholdPercentageT312_r17__cond (SuccessHO_Config_r17__thresholdPercentageT312_r17 z) /\
  opt_cond SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__cond (SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17 z) /\
  True) /\ 
(  True).


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
Definition SuccessHO_Config_r17__thresholdPercentageT304_r17__Format : T_Format SuccessHO_Config_r17__thresholdPercentageT304_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SuccessHO_Config_r17__thresholdPercentageT304_r17__nat__Format SuccessHO_Config_r17__thresholdPercentageT304_r17__F1 SuccessHO_Config_r17__thresholdPercentageT304_r17__F2 SuccessHO_Config_r17__thresholdPercentageT304_r17__F1F2 SuccessHO_Config_r17__thresholdPercentageT304_r17__F2F1.

Opaque SuccessHO_Config_r17__thresholdPercentageT304_r17__cond SuccessHO_Config_r17__thresholdPercentageT304_r17__Format.

Definition SuccessHO_Config_r17__thresholdPercentageT310_r17__Format : T_Format SuccessHO_Config_r17__thresholdPercentageT310_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SuccessHO_Config_r17__thresholdPercentageT310_r17__nat__Format SuccessHO_Config_r17__thresholdPercentageT310_r17__F1 SuccessHO_Config_r17__thresholdPercentageT310_r17__F2 SuccessHO_Config_r17__thresholdPercentageT310_r17__F1F2 SuccessHO_Config_r17__thresholdPercentageT310_r17__F2F1.

Opaque SuccessHO_Config_r17__thresholdPercentageT310_r17__cond SuccessHO_Config_r17__thresholdPercentageT310_r17__Format.

Definition SuccessHO_Config_r17__thresholdPercentageT312_r17__Format : T_Format SuccessHO_Config_r17__thresholdPercentageT312_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SuccessHO_Config_r17__thresholdPercentageT312_r17__nat__Format SuccessHO_Config_r17__thresholdPercentageT312_r17__F1 SuccessHO_Config_r17__thresholdPercentageT312_r17__F2 SuccessHO_Config_r17__thresholdPercentageT312_r17__F1F2 SuccessHO_Config_r17__thresholdPercentageT312_r17__F2F1.

Opaque SuccessHO_Config_r17__thresholdPercentageT312_r17__cond SuccessHO_Config_r17__thresholdPercentageT312_r17__Format.

Definition SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Format : T_Format SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__nat__Format SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F1 SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F2 SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F1F2 SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__F2F1.

Opaque SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__cond SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Format.


Definition SuccessHO_Config_r17__root_Format_Type := Eval cbn in seq_format_prod SuccessHO_Config_r17__root_list.
Definition SuccessHO_Config_r17__root_Format_list : SuccessHO_Config_r17__root_Format_Type :=
  (SuccessHO_Config_r17__thresholdPercentageT304_r17__Format, (SuccessHO_Config_r17__thresholdPercentageT310_r17__Format, (SuccessHO_Config_r17__thresholdPercentageT312_r17__Format, (SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17__Format, unit_format)))).

Definition SuccessHO_Config_r17__ext_Format_Type := Eval cbn in get_formats SuccessHO_Config_r17__ext_list.
Definition SuccessHO_Config_r17__ext_Format_list : SuccessHO_Config_r17__ext_Format_Type :=
  unit__Format.

Definition SuccessHO_Config_r17__list_type : Set := (seq_type SuccessHO_Config_r17__root_list) * (seq_ext_type SuccessHO_Config_r17__ext_list).
Definition SuccessHO_Config_r17__list_cond (z : SuccessHO_Config_r17__list_type) : Prop :=
        (seq_cond SuccessHO_Config_r17__root_list (fst z)) /\ (seq_ext_cond SuccessHO_Config_r17__ext_list (snd z)).
Definition SuccessHO_Config_r17__list_format : T_Format SuccessHO_Config_r17__list_type SuccessHO_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SuccessHO_Config_r17__root_list SuccessHO_Config_r17__root_Format_list SuccessHO_Config_r17__ext_list SuccessHO_Config_r17__ext_Format_list.

Opaque SuccessHO_Config_r17__list_format.
Definition SuccessHO_Config_r17__F1 (z : SuccessHO_Config_r17__Type) : SuccessHO_Config_r17__list_type :=
  (((SuccessHO_Config_r17__thresholdPercentageT304_r17 z, (SuccessHO_Config_r17__thresholdPercentageT310_r17 z, (SuccessHO_Config_r17__thresholdPercentageT312_r17 z, (SuccessHO_Config_r17__sourceDAPS_FailureReporting_r17 z, tt))))), (
tt)).
Definition SuccessHO_Config_r17__F2 (y : SuccessHO_Config_r17__list_type) : SuccessHO_Config_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SuccessHO_Config_r17__Type j0 j1 j2 j3
  end.
Definition SuccessHO_Config_r17__helper1 : (forall a : SuccessHO_Config_r17__Type, SuccessHO_Config_r17__cond a -> SuccessHO_Config_r17__list_cond (SuccessHO_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SuccessHO_Config_r17__helper2 : (forall a : SuccessHO_Config_r17__Type, SuccessHO_Config_r17__F2 (SuccessHO_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SuccessHO_Config_r17__helper3 : (forall b : SuccessHO_Config_r17__list_type, SuccessHO_Config_r17__list_cond b -> SuccessHO_Config_r17__cond (SuccessHO_Config_r17__F2 b) /\ SuccessHO_Config_r17__F1 (SuccessHO_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SuccessHO_Config_r17__cond, SuccessHO_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SuccessHO_Config_r17__Format : T_Format SuccessHO_Config_r17__Type SuccessHO_Config_r17__cond :=
 proj2_format SuccessHO_Config_r17__cond SuccessHO_Config_r17__list_format  SuccessHO_Config_r17__F1 SuccessHO_Config_r17__F2 SuccessHO_Config_r17__helper1 SuccessHO_Config_r17__helper2 SuccessHO_Config_r17__helper3.

Opaque SuccessHO_Config_r17__cond SuccessHO_Config_r17__Format.

