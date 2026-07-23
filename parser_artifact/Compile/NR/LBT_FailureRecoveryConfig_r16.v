Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Type : Set :=
 | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n4
 | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n8
 | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n16
 | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n32
 | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n64
 | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n128
.
Definition LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__cond := (fun (_ : LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Type) => True).
Lemma LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__nat__helper.

Definition LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F1 t :=
  match t with
  | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n4 => 0
  | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n8 => 1
  | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n16 => 2
  | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n32 => 3
  | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n64 => 4
  | LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n128 => 5
  end.
Definition LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F2 n :=
  match n with
  | 0 => LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n4
  | 1 => LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n8
  | 2 => LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n16
  | 3 => LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n32
  | 4 => LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n64
  | 5 => LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n128
  | _ => LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__n4
  end.
Lemma LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F1F2 : forall x : LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Type, (LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F1 x <= 5) /\ LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F2 (LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F1 x) = x. imp_solve. Qed.
Lemma LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F2F1 : forall (y : nat) (H : y <= 5), LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F1 (LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F2 y) = y. enum_solve H y. Qed.

Inductive LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Type : Set :=
 | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms10
 | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms20
 | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms40
 | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms80
 | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms160
 | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms320
.
Definition LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__cond := (fun (_ : LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Type) => True).
Lemma LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__nat__helper.

Definition LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F1 t :=
  match t with
  | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms10 => 0
  | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms20 => 1
  | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms40 => 2
  | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms80 => 3
  | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms160 => 4
  | LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms320 => 5
  end.
Definition LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F2 n :=
  match n with
  | 0 => LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms10
  | 1 => LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms20
  | 2 => LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms40
  | 3 => LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms80
  | 4 => LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms160
  | 5 => LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms320
  | _ => LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__ms10
  end.
Lemma LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F1F2 : forall x : LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Type, (LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F1 x <= 5) /\ LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F2 (LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F1 x) = x. imp_solve. Qed.
Lemma LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F2F1 : forall (y : nat) (H : y <= 5), LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F1 (LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F2 y) = y. enum_solve H y. Qed.

Record LBT_FailureRecoveryConfig_r16__Type : Set :=
  make__LBT_FailureRecoveryConfig_r16__Type {
    LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16 : LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Type ;
    LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16 : LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Type ;
}.
Definition LBT_FailureRecoveryConfig_r16__root_list : list seq_elem := (
 Nor LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Type LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__cond ::
 Nor LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Type LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__cond ::
 nil).
Definition LBT_FailureRecoveryConfig_r16__ext_list : list typ := (
  nil).
Definition LBT_FailureRecoveryConfig_r16__cond (z : LBT_FailureRecoveryConfig_r16__Type) := 
(  LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__cond (LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16 z) /\
  LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__cond (LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16 z) /\
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
Definition LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Format : T_Format LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__nat__Format LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F1 LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F2 LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F1F2 LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__F2F1.

Opaque LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__cond LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Format.

Definition LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Format : T_Format LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__nat__Format LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F1 LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F2 LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F1F2 LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__F2F1.

Opaque LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__cond LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Format.


Definition LBT_FailureRecoveryConfig_r16__root_Format_Type := Eval cbn in seq_format_prod LBT_FailureRecoveryConfig_r16__root_list.
Definition LBT_FailureRecoveryConfig_r16__root_Format_list : LBT_FailureRecoveryConfig_r16__root_Format_Type :=
  (LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16__Format, (LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16__Format, unit_format)).

Definition LBT_FailureRecoveryConfig_r16__ext_Format_Type := Eval cbn in get_formats LBT_FailureRecoveryConfig_r16__ext_list.
Definition LBT_FailureRecoveryConfig_r16__ext_Format_list : LBT_FailureRecoveryConfig_r16__ext_Format_Type :=
  unit__Format.

Definition LBT_FailureRecoveryConfig_r16__list_type : Set := (seq_type LBT_FailureRecoveryConfig_r16__root_list) * (seq_ext_type LBT_FailureRecoveryConfig_r16__ext_list).
Definition LBT_FailureRecoveryConfig_r16__list_cond (z : LBT_FailureRecoveryConfig_r16__list_type) : Prop :=
        (seq_cond LBT_FailureRecoveryConfig_r16__root_list (fst z)) /\ (seq_ext_cond LBT_FailureRecoveryConfig_r16__ext_list (snd z)).
Definition LBT_FailureRecoveryConfig_r16__list_format : T_Format LBT_FailureRecoveryConfig_r16__list_type LBT_FailureRecoveryConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format LBT_FailureRecoveryConfig_r16__root_list LBT_FailureRecoveryConfig_r16__root_Format_list LBT_FailureRecoveryConfig_r16__ext_list LBT_FailureRecoveryConfig_r16__ext_Format_list.

Opaque LBT_FailureRecoveryConfig_r16__list_format.
Definition LBT_FailureRecoveryConfig_r16__F1 (z : LBT_FailureRecoveryConfig_r16__Type) : LBT_FailureRecoveryConfig_r16__list_type :=
  (((LBT_FailureRecoveryConfig_r16__lbt_FailureInstanceMaxCount_r16 z, (LBT_FailureRecoveryConfig_r16__lbt_FailureDetectionTimer_r16 z, tt))), (
tt)).
Definition LBT_FailureRecoveryConfig_r16__F2 (y : LBT_FailureRecoveryConfig_r16__list_type) : LBT_FailureRecoveryConfig_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__LBT_FailureRecoveryConfig_r16__Type j0 j1
  end.
Definition LBT_FailureRecoveryConfig_r16__helper1 : (forall a : LBT_FailureRecoveryConfig_r16__Type, LBT_FailureRecoveryConfig_r16__cond a -> LBT_FailureRecoveryConfig_r16__list_cond (LBT_FailureRecoveryConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition LBT_FailureRecoveryConfig_r16__helper2 : (forall a : LBT_FailureRecoveryConfig_r16__Type, LBT_FailureRecoveryConfig_r16__F2 (LBT_FailureRecoveryConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition LBT_FailureRecoveryConfig_r16__helper3 : (forall b : LBT_FailureRecoveryConfig_r16__list_type, LBT_FailureRecoveryConfig_r16__list_cond b -> LBT_FailureRecoveryConfig_r16__cond (LBT_FailureRecoveryConfig_r16__F2 b) /\ LBT_FailureRecoveryConfig_r16__F1 (LBT_FailureRecoveryConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold LBT_FailureRecoveryConfig_r16__cond, LBT_FailureRecoveryConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition LBT_FailureRecoveryConfig_r16__Format : T_Format LBT_FailureRecoveryConfig_r16__Type LBT_FailureRecoveryConfig_r16__cond :=
 proj2_format LBT_FailureRecoveryConfig_r16__cond LBT_FailureRecoveryConfig_r16__list_format  LBT_FailureRecoveryConfig_r16__F1 LBT_FailureRecoveryConfig_r16__F2 LBT_FailureRecoveryConfig_r16__helper1 LBT_FailureRecoveryConfig_r16__helper2 LBT_FailureRecoveryConfig_r16__helper3.

Opaque LBT_FailureRecoveryConfig_r16__cond LBT_FailureRecoveryConfig_r16__Format.

