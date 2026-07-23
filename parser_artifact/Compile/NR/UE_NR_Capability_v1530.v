Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UE_NR_CapabilityAddXDD_Mode_v1530.

Opaque UE_NR_CapabilityAddXDD_Mode_v1530__cond UE_NR_CapabilityAddXDD_Mode_v1530__Format.

Require Import NR.UE_NR_CapabilityAddXDD_Mode_v1530.

Opaque UE_NR_CapabilityAddXDD_Mode_v1530__cond UE_NR_CapabilityAddXDD_Mode_v1530__Format.

Inductive UE_NR_Capability_v1530__dummy__Type : Set :=
 | UE_NR_Capability_v1530__dummy__supported
.
Definition UE_NR_Capability_v1530__dummy__cond := (fun (_ : UE_NR_Capability_v1530__dummy__Type) => True).
Lemma UE_NR_Capability_v1530__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1530__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1530__dummy__nat__helper.

Definition UE_NR_Capability_v1530__dummy__F1 t :=
  match t with
  | UE_NR_Capability_v1530__dummy__supported => 0
  end.
Definition UE_NR_Capability_v1530__dummy__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1530__dummy__supported
  | _ => UE_NR_Capability_v1530__dummy__supported
  end.
Lemma UE_NR_Capability_v1530__dummy__F1F2 : forall x : UE_NR_Capability_v1530__dummy__Type, (UE_NR_Capability_v1530__dummy__F1 x <= 0) /\ UE_NR_Capability_v1530__dummy__F2 (UE_NR_Capability_v1530__dummy__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1530__dummy__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1530__dummy__F1 (UE_NR_Capability_v1530__dummy__F2 y) = y. enum_solve H y. Qed.

Require Import NR.InterRAT_Parameters.

Opaque InterRAT_Parameters__cond InterRAT_Parameters__Format.

Inductive UE_NR_Capability_v1530__inactiveState__Type : Set :=
 | UE_NR_Capability_v1530__inactiveState__supported
.
Definition UE_NR_Capability_v1530__inactiveState__cond := (fun (_ : UE_NR_Capability_v1530__inactiveState__Type) => True).
Lemma UE_NR_Capability_v1530__inactiveState__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1530__inactiveState__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1530__inactiveState__nat__helper.

Definition UE_NR_Capability_v1530__inactiveState__F1 t :=
  match t with
  | UE_NR_Capability_v1530__inactiveState__supported => 0
  end.
Definition UE_NR_Capability_v1530__inactiveState__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1530__inactiveState__supported
  | _ => UE_NR_Capability_v1530__inactiveState__supported
  end.
Lemma UE_NR_Capability_v1530__inactiveState__F1F2 : forall x : UE_NR_Capability_v1530__inactiveState__Type, (UE_NR_Capability_v1530__inactiveState__F1 x <= 0) /\ UE_NR_Capability_v1530__inactiveState__F2 (UE_NR_Capability_v1530__inactiveState__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1530__inactiveState__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1530__inactiveState__F1 (UE_NR_Capability_v1530__inactiveState__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1530__delayBudgetReporting__Type : Set :=
 | UE_NR_Capability_v1530__delayBudgetReporting__supported
.
Definition UE_NR_Capability_v1530__delayBudgetReporting__cond := (fun (_ : UE_NR_Capability_v1530__delayBudgetReporting__Type) => True).
Lemma UE_NR_Capability_v1530__delayBudgetReporting__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1530__delayBudgetReporting__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1530__delayBudgetReporting__nat__helper.

Definition UE_NR_Capability_v1530__delayBudgetReporting__F1 t :=
  match t with
  | UE_NR_Capability_v1530__delayBudgetReporting__supported => 0
  end.
Definition UE_NR_Capability_v1530__delayBudgetReporting__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1530__delayBudgetReporting__supported
  | _ => UE_NR_Capability_v1530__delayBudgetReporting__supported
  end.
Lemma UE_NR_Capability_v1530__delayBudgetReporting__F1F2 : forall x : UE_NR_Capability_v1530__delayBudgetReporting__Type, (UE_NR_Capability_v1530__delayBudgetReporting__F1 x <= 0) /\ UE_NR_Capability_v1530__delayBudgetReporting__F2 (UE_NR_Capability_v1530__delayBudgetReporting__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1530__delayBudgetReporting__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1530__delayBudgetReporting__F1 (UE_NR_Capability_v1530__delayBudgetReporting__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UE_NR_Capability_v1540.

Opaque UE_NR_Capability_v1540__cond UE_NR_Capability_v1540__Format.

Record UE_NR_Capability_v1530__Type : Set :=
  make__UE_NR_Capability_v1530__Type {
    UE_NR_Capability_v1530__fdd_Add_UE_NR_Capabilities_v1530 : option UE_NR_CapabilityAddXDD_Mode_v1530__Type ;
    UE_NR_Capability_v1530__tdd_Add_UE_NR_Capabilities_v1530 : option UE_NR_CapabilityAddXDD_Mode_v1530__Type ;
    UE_NR_Capability_v1530__dummy : option UE_NR_Capability_v1530__dummy__Type ;
    UE_NR_Capability_v1530__interRAT_Parameters : option InterRAT_Parameters__Type ;
    UE_NR_Capability_v1530__inactiveState : option UE_NR_Capability_v1530__inactiveState__Type ;
    UE_NR_Capability_v1530__delayBudgetReporting : option UE_NR_Capability_v1530__delayBudgetReporting__Type ;
    UE_NR_Capability_v1530__nonCriticalExtension : option UE_NR_Capability_v1540__Type ;
}.
Definition UE_NR_Capability_v1530__list := (
 Opt UE_NR_CapabilityAddXDD_Mode_v1530__Type UE_NR_CapabilityAddXDD_Mode_v1530__cond ::
 Opt UE_NR_CapabilityAddXDD_Mode_v1530__Type UE_NR_CapabilityAddXDD_Mode_v1530__cond ::
 Opt UE_NR_Capability_v1530__dummy__Type UE_NR_Capability_v1530__dummy__cond ::
 Opt InterRAT_Parameters__Type InterRAT_Parameters__cond ::
 Opt UE_NR_Capability_v1530__inactiveState__Type UE_NR_Capability_v1530__inactiveState__cond ::
 Opt UE_NR_Capability_v1530__delayBudgetReporting__Type UE_NR_Capability_v1530__delayBudgetReporting__cond ::
 Opt UE_NR_Capability_v1540__Type UE_NR_Capability_v1540__cond ::
 nil).
Definition UE_NR_Capability_v1530__cond z := 
  opt_cond UE_NR_CapabilityAddXDD_Mode_v1530__cond (UE_NR_Capability_v1530__fdd_Add_UE_NR_Capabilities_v1530 z) /\
  opt_cond UE_NR_CapabilityAddXDD_Mode_v1530__cond (UE_NR_Capability_v1530__tdd_Add_UE_NR_Capabilities_v1530 z) /\
  opt_cond UE_NR_Capability_v1530__dummy__cond (UE_NR_Capability_v1530__dummy z) /\
  opt_cond InterRAT_Parameters__cond (UE_NR_Capability_v1530__interRAT_Parameters z) /\
  opt_cond UE_NR_Capability_v1530__inactiveState__cond (UE_NR_Capability_v1530__inactiveState z) /\
  opt_cond UE_NR_Capability_v1530__delayBudgetReporting__cond (UE_NR_Capability_v1530__delayBudgetReporting z) /\
  opt_cond UE_NR_Capability_v1540__cond (UE_NR_Capability_v1530__nonCriticalExtension z) /\
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
Definition UE_NR_Capability_v1530__dummy__Format : T_Format UE_NR_Capability_v1530__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1530__dummy__nat__Format UE_NR_Capability_v1530__dummy__F1 UE_NR_Capability_v1530__dummy__F2 UE_NR_Capability_v1530__dummy__F1F2 UE_NR_Capability_v1530__dummy__F2F1.

Opaque UE_NR_Capability_v1530__dummy__cond UE_NR_Capability_v1530__dummy__Format.

Definition UE_NR_Capability_v1530__inactiveState__Format : T_Format UE_NR_Capability_v1530__inactiveState__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1530__inactiveState__nat__Format UE_NR_Capability_v1530__inactiveState__F1 UE_NR_Capability_v1530__inactiveState__F2 UE_NR_Capability_v1530__inactiveState__F1F2 UE_NR_Capability_v1530__inactiveState__F2F1.

Opaque UE_NR_Capability_v1530__inactiveState__cond UE_NR_Capability_v1530__inactiveState__Format.

Definition UE_NR_Capability_v1530__delayBudgetReporting__Format : T_Format UE_NR_Capability_v1530__delayBudgetReporting__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1530__delayBudgetReporting__nat__Format UE_NR_Capability_v1530__delayBudgetReporting__F1 UE_NR_Capability_v1530__delayBudgetReporting__F2 UE_NR_Capability_v1530__delayBudgetReporting__F1F2 UE_NR_Capability_v1530__delayBudgetReporting__F2F1.

Opaque UE_NR_Capability_v1530__delayBudgetReporting__cond UE_NR_Capability_v1530__delayBudgetReporting__Format.


Definition UE_NR_Capability_v1530__Format_Type := Eval cbn in seq_format_prod UE_NR_Capability_v1530__list.
Definition UE_NR_Capability_v1530__Format_list : UE_NR_Capability_v1530__Format_Type :=
  (UE_NR_CapabilityAddXDD_Mode_v1530__Format, (UE_NR_CapabilityAddXDD_Mode_v1530__Format, (UE_NR_Capability_v1530__dummy__Format, (InterRAT_Parameters__Format, (UE_NR_Capability_v1530__inactiveState__Format, (UE_NR_Capability_v1530__delayBudgetReporting__Format, (UE_NR_Capability_v1540__Format, unit_format))))))).
Definition UE_NR_Capability_v1530__list__Format := (*Eval compute in *) seq_format UE_NR_Capability_v1530__list UE_NR_Capability_v1530__Format_list.
Definition UE_NR_Capability_v1530__F1 z :=
  (UE_NR_Capability_v1530__fdd_Add_UE_NR_Capabilities_v1530 z, (UE_NR_Capability_v1530__tdd_Add_UE_NR_Capabilities_v1530 z, (UE_NR_Capability_v1530__dummy z, (UE_NR_Capability_v1530__interRAT_Parameters z, (UE_NR_Capability_v1530__inactiveState z, (UE_NR_Capability_v1530__delayBudgetReporting z, (UE_NR_Capability_v1530__nonCriticalExtension z, tt))))))).
Definition UE_NR_Capability_v1530__F2 (y : seq_type UE_NR_Capability_v1530__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__UE_NR_Capability_v1530__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma UE_NR_Capability_v1530__F1F2_cond (z : UE_NR_Capability_v1530__Type)
  : UE_NR_Capability_v1530__cond z ->
  (seq_cond UE_NR_Capability_v1530__list (UE_NR_Capability_v1530__F1 z)).
intro H. unfold UE_NR_Capability_v1530__cond in H. simpl. auto. Qed.
Lemma UE_NR_Capability_v1530__F1F2_cond2 (z : UE_NR_Capability_v1530__Type)
 : UE_NR_Capability_v1530__F2 (UE_NR_Capability_v1530__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_NR_Capability_v1530__F2F1_cond (y : seq_type UE_NR_Capability_v1530__list)
  : seq_cond UE_NR_Capability_v1530__list y ->
 (UE_NR_Capability_v1530__cond (UE_NR_Capability_v1530__F2 y)) /\  UE_NR_Capability_v1530__F1 (UE_NR_Capability_v1530__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_NR_Capability_v1530__cond. simpl in *. auto.
 - simpl. unfold UE_NR_Capability_v1530__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_NR_Capability_v1530__Format : T_Format UE_NR_Capability_v1530__Type UE_NR_Capability_v1530__cond :=
        proj2_format  UE_NR_Capability_v1530__cond UE_NR_Capability_v1530__list__Format
    UE_NR_Capability_v1530__F1 UE_NR_Capability_v1530__F2 UE_NR_Capability_v1530__F1F2_cond  UE_NR_Capability_v1530__F1F2_cond2 UE_NR_Capability_v1530__F2F1_cond.
Opaque UE_NR_Capability_v1530__cond UE_NR_Capability_v1530__Format.

