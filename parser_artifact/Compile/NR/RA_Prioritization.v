Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RA_Prioritization__powerRampingStepHighPriority__Type : Set :=
 | RA_Prioritization__powerRampingStepHighPriority__dB0
 | RA_Prioritization__powerRampingStepHighPriority__dB2
 | RA_Prioritization__powerRampingStepHighPriority__dB4
 | RA_Prioritization__powerRampingStepHighPriority__dB6
.
Definition RA_Prioritization__powerRampingStepHighPriority__cond := (fun (_ : RA_Prioritization__powerRampingStepHighPriority__Type) => True).
Lemma RA_Prioritization__powerRampingStepHighPriority__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_Prioritization__powerRampingStepHighPriority__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_Prioritization__powerRampingStepHighPriority__nat__helper.

Definition RA_Prioritization__powerRampingStepHighPriority__F1 t :=
  match t with
  | RA_Prioritization__powerRampingStepHighPriority__dB0 => 0
  | RA_Prioritization__powerRampingStepHighPriority__dB2 => 1
  | RA_Prioritization__powerRampingStepHighPriority__dB4 => 2
  | RA_Prioritization__powerRampingStepHighPriority__dB6 => 3
  end.
Definition RA_Prioritization__powerRampingStepHighPriority__F2 n :=
  match n with
  | 0 => RA_Prioritization__powerRampingStepHighPriority__dB0
  | 1 => RA_Prioritization__powerRampingStepHighPriority__dB2
  | 2 => RA_Prioritization__powerRampingStepHighPriority__dB4
  | 3 => RA_Prioritization__powerRampingStepHighPriority__dB6
  | _ => RA_Prioritization__powerRampingStepHighPriority__dB0
  end.
Lemma RA_Prioritization__powerRampingStepHighPriority__F1F2 : forall x : RA_Prioritization__powerRampingStepHighPriority__Type, (RA_Prioritization__powerRampingStepHighPriority__F1 x <= 3) /\ RA_Prioritization__powerRampingStepHighPriority__F2 (RA_Prioritization__powerRampingStepHighPriority__F1 x) = x. imp_solve. Qed.
Lemma RA_Prioritization__powerRampingStepHighPriority__F2F1 : forall (y : nat) (H : y <= 3), RA_Prioritization__powerRampingStepHighPriority__F1 (RA_Prioritization__powerRampingStepHighPriority__F2 y) = y. enum_solve H y. Qed.

Inductive RA_Prioritization__scalingFactorBI__Type : Set :=
 | RA_Prioritization__scalingFactorBI__zero
 | RA_Prioritization__scalingFactorBI__dot25
 | RA_Prioritization__scalingFactorBI__dot5
 | RA_Prioritization__scalingFactorBI__dot75
.
Definition RA_Prioritization__scalingFactorBI__cond := (fun (_ : RA_Prioritization__scalingFactorBI__Type) => True).
Lemma RA_Prioritization__scalingFactorBI__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_Prioritization__scalingFactorBI__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_Prioritization__scalingFactorBI__nat__helper.

Definition RA_Prioritization__scalingFactorBI__F1 t :=
  match t with
  | RA_Prioritization__scalingFactorBI__zero => 0
  | RA_Prioritization__scalingFactorBI__dot25 => 1
  | RA_Prioritization__scalingFactorBI__dot5 => 2
  | RA_Prioritization__scalingFactorBI__dot75 => 3
  end.
Definition RA_Prioritization__scalingFactorBI__F2 n :=
  match n with
  | 0 => RA_Prioritization__scalingFactorBI__zero
  | 1 => RA_Prioritization__scalingFactorBI__dot25
  | 2 => RA_Prioritization__scalingFactorBI__dot5
  | 3 => RA_Prioritization__scalingFactorBI__dot75
  | _ => RA_Prioritization__scalingFactorBI__zero
  end.
Lemma RA_Prioritization__scalingFactorBI__F1F2 : forall x : RA_Prioritization__scalingFactorBI__Type, (RA_Prioritization__scalingFactorBI__F1 x <= 3) /\ RA_Prioritization__scalingFactorBI__F2 (RA_Prioritization__scalingFactorBI__F1 x) = x. imp_solve. Qed.
Lemma RA_Prioritization__scalingFactorBI__F2F1 : forall (y : nat) (H : y <= 3), RA_Prioritization__scalingFactorBI__F1 (RA_Prioritization__scalingFactorBI__F2 y) = y. enum_solve H y. Qed.

Record RA_Prioritization__Type : Set :=
  make__RA_Prioritization__Type {
    RA_Prioritization__powerRampingStepHighPriority : RA_Prioritization__powerRampingStepHighPriority__Type ;
    RA_Prioritization__scalingFactorBI : option RA_Prioritization__scalingFactorBI__Type ;
}.
Definition RA_Prioritization__root_list : list seq_elem := (
 Nor RA_Prioritization__powerRampingStepHighPriority__Type RA_Prioritization__powerRampingStepHighPriority__cond ::
 Opt RA_Prioritization__scalingFactorBI__Type RA_Prioritization__scalingFactorBI__cond ::
 nil).
Definition RA_Prioritization__ext_list : list typ := (
  nil).
Definition RA_Prioritization__cond (z : RA_Prioritization__Type) := 
(  RA_Prioritization__powerRampingStepHighPriority__cond (RA_Prioritization__powerRampingStepHighPriority z) /\
  opt_cond RA_Prioritization__scalingFactorBI__cond (RA_Prioritization__scalingFactorBI z) /\
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
Definition RA_Prioritization__powerRampingStepHighPriority__Format : T_Format RA_Prioritization__powerRampingStepHighPriority__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_Prioritization__powerRampingStepHighPriority__nat__Format RA_Prioritization__powerRampingStepHighPriority__F1 RA_Prioritization__powerRampingStepHighPriority__F2 RA_Prioritization__powerRampingStepHighPriority__F1F2 RA_Prioritization__powerRampingStepHighPriority__F2F1.

Opaque RA_Prioritization__powerRampingStepHighPriority__cond RA_Prioritization__powerRampingStepHighPriority__Format.

Definition RA_Prioritization__scalingFactorBI__Format : T_Format RA_Prioritization__scalingFactorBI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_Prioritization__scalingFactorBI__nat__Format RA_Prioritization__scalingFactorBI__F1 RA_Prioritization__scalingFactorBI__F2 RA_Prioritization__scalingFactorBI__F1F2 RA_Prioritization__scalingFactorBI__F2F1.

Opaque RA_Prioritization__scalingFactorBI__cond RA_Prioritization__scalingFactorBI__Format.


Definition RA_Prioritization__root_Format_Type := Eval cbn in seq_format_prod RA_Prioritization__root_list.
Definition RA_Prioritization__root_Format_list : RA_Prioritization__root_Format_Type :=
  (RA_Prioritization__powerRampingStepHighPriority__Format, (RA_Prioritization__scalingFactorBI__Format, unit_format)).

Definition RA_Prioritization__ext_Format_Type := Eval cbn in get_formats RA_Prioritization__ext_list.
Definition RA_Prioritization__ext_Format_list : RA_Prioritization__ext_Format_Type :=
  unit__Format.

Definition RA_Prioritization__list_type : Set := (seq_type RA_Prioritization__root_list) * (seq_ext_type RA_Prioritization__ext_list).
Definition RA_Prioritization__list_cond (z : RA_Prioritization__list_type) : Prop :=
        (seq_cond RA_Prioritization__root_list (fst z)) /\ (seq_ext_cond RA_Prioritization__ext_list (snd z)).
Definition RA_Prioritization__list_format : T_Format RA_Prioritization__list_type RA_Prioritization__list_cond :=
 (* Eval compute in *) seq_ext_format RA_Prioritization__root_list RA_Prioritization__root_Format_list RA_Prioritization__ext_list RA_Prioritization__ext_Format_list.

Opaque RA_Prioritization__list_format.
Definition RA_Prioritization__F1 (z : RA_Prioritization__Type) : RA_Prioritization__list_type :=
  (((RA_Prioritization__powerRampingStepHighPriority z, (RA_Prioritization__scalingFactorBI z, tt))), (
tt)).
Definition RA_Prioritization__F2 (y : RA_Prioritization__list_type) : RA_Prioritization__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__RA_Prioritization__Type j0 j1
  end.
Definition RA_Prioritization__helper1 : (forall a : RA_Prioritization__Type, RA_Prioritization__cond a -> RA_Prioritization__list_cond (RA_Prioritization__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RA_Prioritization__helper2 : (forall a : RA_Prioritization__Type, RA_Prioritization__F2 (RA_Prioritization__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RA_Prioritization__helper3 : (forall b : RA_Prioritization__list_type, RA_Prioritization__list_cond b -> RA_Prioritization__cond (RA_Prioritization__F2 b) /\ RA_Prioritization__F1 (RA_Prioritization__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RA_Prioritization__cond, RA_Prioritization__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RA_Prioritization__Format : T_Format RA_Prioritization__Type RA_Prioritization__cond :=
 proj2_format RA_Prioritization__cond RA_Prioritization__list_format  RA_Prioritization__F1 RA_Prioritization__F2 RA_Prioritization__helper1 RA_Prioritization__helper2 RA_Prioritization__helper3.

Opaque RA_Prioritization__cond RA_Prioritization__Format.

