Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Type : Set :=
 | HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__set1
 | HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__set2
.
Definition HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__cond := (fun (_ : HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Type) => True).
Lemma HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__nat__helper.

Definition HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F1 t :=
  match t with
  | HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__set1 => 0
  | HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__set2 => 1
  end.
Definition HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F2 n :=
  match n with
  | 0 => HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__set1
  | 1 => HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__set2
  | _ => HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__set1
  end.
Lemma HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F1F2 : forall x : HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Type, (HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F1 x <= 1) /\ HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F2 (HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F1 x) = x. imp_solve. Qed.
Lemma HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F2F1 : forall (y : nat) (H : y <= 1), HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F1 (HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Type : Set :=
 | HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__unidirectional
 | HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__bidirectional
.
Definition HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__cond := (fun (_ : HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Type) => True).
Lemma HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__nat__helper.

Definition HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F1 t :=
  match t with
  | HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__unidirectional => 0
  | HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__bidirectional => 1
  end.
Definition HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F2 n :=
  match n with
  | 0 => HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__unidirectional
  | 1 => HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__bidirectional
  | _ => HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__unidirectional
  end.
Lemma HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F1F2 : forall x : HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Type, (HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F1 x <= 1) /\ HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F2 (HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F1 x) = x. imp_solve. Qed.
Lemma HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F2F1 : forall (y : nat) (H : y <= 1), HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F1 (HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Type : Set :=
 | HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__true
.
Definition HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__cond := (fun (_ : HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Type) => True).
Lemma HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__nat__helper.

Definition HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F1 t :=
  match t with
  | HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__true => 0
  end.
Definition HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F2 n :=
  match n with
  | 0 => HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__true
  | _ => HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__true
  end.
Lemma HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F1F2 : forall x : HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Type, (HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F1 x <= 0) /\ HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F2 (HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F1 x) = x. imp_solve. Qed.
Lemma HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F2F1 : forall (y : nat) (H : y <= 0), HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F1 (HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F2 y) = y. enum_solve H y. Qed.

Record HighSpeedConfigFR2_r17__Type : Set :=
  make__HighSpeedConfigFR2_r17__Type {
    HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17 : option HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Type ;
    HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17 : option HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Type ;
    HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17 : option HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Type ;
}.
Definition HighSpeedConfigFR2_r17__root_list : list seq_elem := (
 Opt HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Type HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__cond ::
 Opt HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Type HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__cond ::
 Opt HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Type HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__cond ::
 nil).
Definition HighSpeedConfigFR2_r17__ext_list : list typ := (
  nil).
Definition HighSpeedConfigFR2_r17__cond (z : HighSpeedConfigFR2_r17__Type) := 
(  opt_cond HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__cond (HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17 z) /\
  opt_cond HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__cond (HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17 z) /\
  opt_cond HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__cond (HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17 z) /\
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
Definition HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Format : T_Format HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__nat__Format HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F1 HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F2 HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F1F2 HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__F2F1.

Opaque HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__cond HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Format.

Definition HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Format : T_Format HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__nat__Format HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F1 HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F2 HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F1F2 HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__F2F1.

Opaque HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__cond HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Format.

Definition HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Format : T_Format HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__nat__Format HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F1 HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F2 HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F1F2 HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__F2F1.

Opaque HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__cond HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Format.


Definition HighSpeedConfigFR2_r17__root_Format_Type := Eval cbn in seq_format_prod HighSpeedConfigFR2_r17__root_list.
Definition HighSpeedConfigFR2_r17__root_Format_list : HighSpeedConfigFR2_r17__root_Format_Type :=
  (HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17__Format, (HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17__Format, (HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17__Format, unit_format))).

Definition HighSpeedConfigFR2_r17__ext_Format_Type := Eval cbn in get_formats HighSpeedConfigFR2_r17__ext_list.
Definition HighSpeedConfigFR2_r17__ext_Format_list : HighSpeedConfigFR2_r17__ext_Format_Type :=
  unit__Format.

Definition HighSpeedConfigFR2_r17__list_type : Set := (seq_type HighSpeedConfigFR2_r17__root_list) * (seq_ext_type HighSpeedConfigFR2_r17__ext_list).
Definition HighSpeedConfigFR2_r17__list_cond (z : HighSpeedConfigFR2_r17__list_type) : Prop :=
        (seq_cond HighSpeedConfigFR2_r17__root_list (fst z)) /\ (seq_ext_cond HighSpeedConfigFR2_r17__ext_list (snd z)).
Definition HighSpeedConfigFR2_r17__list_format : T_Format HighSpeedConfigFR2_r17__list_type HighSpeedConfigFR2_r17__list_cond :=
 (* Eval compute in *) seq_ext_format HighSpeedConfigFR2_r17__root_list HighSpeedConfigFR2_r17__root_Format_list HighSpeedConfigFR2_r17__ext_list HighSpeedConfigFR2_r17__ext_Format_list.

Opaque HighSpeedConfigFR2_r17__list_format.
Definition HighSpeedConfigFR2_r17__F1 (z : HighSpeedConfigFR2_r17__Type) : HighSpeedConfigFR2_r17__list_type :=
  (((HighSpeedConfigFR2_r17__highSpeedMeasFlagFR2_r17 z, (HighSpeedConfigFR2_r17__highSpeedDeploymentTypeFR2_r17 z, (HighSpeedConfigFR2_r17__highSpeedLargeOneStepUL_TimingFR2_r17 z, tt)))), (
tt)).
Definition HighSpeedConfigFR2_r17__F2 (y : HighSpeedConfigFR2_r17__list_type) : HighSpeedConfigFR2_r17__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__HighSpeedConfigFR2_r17__Type j0 j1 j2
  end.
Definition HighSpeedConfigFR2_r17__helper1 : (forall a : HighSpeedConfigFR2_r17__Type, HighSpeedConfigFR2_r17__cond a -> HighSpeedConfigFR2_r17__list_cond (HighSpeedConfigFR2_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition HighSpeedConfigFR2_r17__helper2 : (forall a : HighSpeedConfigFR2_r17__Type, HighSpeedConfigFR2_r17__F2 (HighSpeedConfigFR2_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition HighSpeedConfigFR2_r17__helper3 : (forall b : HighSpeedConfigFR2_r17__list_type, HighSpeedConfigFR2_r17__list_cond b -> HighSpeedConfigFR2_r17__cond (HighSpeedConfigFR2_r17__F2 b) /\ HighSpeedConfigFR2_r17__F1 (HighSpeedConfigFR2_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold HighSpeedConfigFR2_r17__cond, HighSpeedConfigFR2_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition HighSpeedConfigFR2_r17__Format : T_Format HighSpeedConfigFR2_r17__Type HighSpeedConfigFR2_r17__cond :=
 proj2_format HighSpeedConfigFR2_r17__cond HighSpeedConfigFR2_r17__list_format  HighSpeedConfigFR2_r17__F1 HighSpeedConfigFR2_r17__F2 HighSpeedConfigFR2_r17__helper1 HighSpeedConfigFR2_r17__helper2 HighSpeedConfigFR2_r17__helper3.

Opaque HighSpeedConfigFR2_r17__cond HighSpeedConfigFR2_r17__Format.

