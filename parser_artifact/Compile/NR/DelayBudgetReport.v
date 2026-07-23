Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DelayBudgetReport__root__type1__Type : Set :=
 | DelayBudgetReport__root__type1__msMinus1280
 | DelayBudgetReport__root__type1__msMinus640
 | DelayBudgetReport__root__type1__msMinus320
 | DelayBudgetReport__root__type1__msMinus160
 | DelayBudgetReport__root__type1__msMinus80
 | DelayBudgetReport__root__type1__msMinus60
 | DelayBudgetReport__root__type1__msMinus40
 | DelayBudgetReport__root__type1__msMinus20
 | DelayBudgetReport__root__type1__ms0
 | DelayBudgetReport__root__type1__ms20
 | DelayBudgetReport__root__type1__ms40
 | DelayBudgetReport__root__type1__ms60
 | DelayBudgetReport__root__type1__ms80
 | DelayBudgetReport__root__type1__ms160
 | DelayBudgetReport__root__type1__ms320
 | DelayBudgetReport__root__type1__ms640
 | DelayBudgetReport__root__type1__ms1280
.
Definition DelayBudgetReport__root__type1__cond := (fun (_ : DelayBudgetReport__root__type1__Type) => True).
Lemma DelayBudgetReport__root__type1__nat__helper : to_bit_sz 16 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DelayBudgetReport__root__type1__nat__Format : T_Format nat (fun z => (z <= 16)) :=
  nat_enum_format 16 DelayBudgetReport__root__type1__nat__helper.

Definition DelayBudgetReport__root__type1__F1 t :=
  match t with
  | DelayBudgetReport__root__type1__msMinus1280 => 0
  | DelayBudgetReport__root__type1__msMinus640 => 1
  | DelayBudgetReport__root__type1__msMinus320 => 2
  | DelayBudgetReport__root__type1__msMinus160 => 3
  | DelayBudgetReport__root__type1__msMinus80 => 4
  | DelayBudgetReport__root__type1__msMinus60 => 5
  | DelayBudgetReport__root__type1__msMinus40 => 6
  | DelayBudgetReport__root__type1__msMinus20 => 7
  | DelayBudgetReport__root__type1__ms0 => 8
  | DelayBudgetReport__root__type1__ms20 => 9
  | DelayBudgetReport__root__type1__ms40 => 10
  | DelayBudgetReport__root__type1__ms60 => 11
  | DelayBudgetReport__root__type1__ms80 => 12
  | DelayBudgetReport__root__type1__ms160 => 13
  | DelayBudgetReport__root__type1__ms320 => 14
  | DelayBudgetReport__root__type1__ms640 => 15
  | DelayBudgetReport__root__type1__ms1280 => 16
  end.
Definition DelayBudgetReport__root__type1__F2 n :=
  match n with
  | 0 => DelayBudgetReport__root__type1__msMinus1280
  | 1 => DelayBudgetReport__root__type1__msMinus640
  | 2 => DelayBudgetReport__root__type1__msMinus320
  | 3 => DelayBudgetReport__root__type1__msMinus160
  | 4 => DelayBudgetReport__root__type1__msMinus80
  | 5 => DelayBudgetReport__root__type1__msMinus60
  | 6 => DelayBudgetReport__root__type1__msMinus40
  | 7 => DelayBudgetReport__root__type1__msMinus20
  | 8 => DelayBudgetReport__root__type1__ms0
  | 9 => DelayBudgetReport__root__type1__ms20
  | 10 => DelayBudgetReport__root__type1__ms40
  | 11 => DelayBudgetReport__root__type1__ms60
  | 12 => DelayBudgetReport__root__type1__ms80
  | 13 => DelayBudgetReport__root__type1__ms160
  | 14 => DelayBudgetReport__root__type1__ms320
  | 15 => DelayBudgetReport__root__type1__ms640
  | 16 => DelayBudgetReport__root__type1__ms1280
  | _ => DelayBudgetReport__root__type1__msMinus1280
  end.
Lemma DelayBudgetReport__root__type1__F1F2 : forall x : DelayBudgetReport__root__type1__Type, (DelayBudgetReport__root__type1__F1 x <= 16) /\ DelayBudgetReport__root__type1__F2 (DelayBudgetReport__root__type1__F1 x) = x. imp_solve. Qed.
Lemma DelayBudgetReport__root__type1__F2F1 : forall (y : nat) (H : y <= 16), DelayBudgetReport__root__type1__F1 (DelayBudgetReport__root__type1__F2 y) = y. enum_solve H y. Qed.


Inductive DelayBudgetReport__root__Type : Set := | DelayBudgetReport__root__type1 : DelayBudgetReport__root__type1__Type -> DelayBudgetReport__root__Type.
Definition DelayBudgetReport__root__cond (c : DelayBudgetReport__root__Type) := 
  match c with
  | DelayBudgetReport__root__type1 t => DelayBudgetReport__root__type1__cond t 
  end.


Definition DelayBudgetReport__ext__Type : Set := Empty_set.
Definition DelayBudgetReport__ext__cond (c : DelayBudgetReport__ext__Type) := True.
Definition DelayBudgetReport__Type : Set := DelayBudgetReport__root__Type + DelayBudgetReport__ext__Type.
Definition DelayBudgetReport__cond :=
  sum_cond DelayBudgetReport__root__cond DelayBudgetReport__ext__cond.

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
Definition DelayBudgetReport__root__type1__Format : T_Format DelayBudgetReport__root__type1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DelayBudgetReport__root__type1__nat__Format DelayBudgetReport__root__type1__F1 DelayBudgetReport__root__type1__F2 DelayBudgetReport__root__type1__F1F2 DelayBudgetReport__root__type1__F2F1.

Opaque DelayBudgetReport__root__type1__cond DelayBudgetReport__root__type1__Format.

Definition DelayBudgetReport__root__F1 (z : DelayBudgetReport__root__Type) : DelayBudgetReport__root__type1__Type := 
  match z with
  | DelayBudgetReport__root__type1 t => t
  end.
Definition DelayBudgetReport__root__F2 (y : DelayBudgetReport__root__type1__Type) : DelayBudgetReport__root__Type := DelayBudgetReport__root__type1 y.

Definition DelayBudgetReport__root__helper2 : (forall z : DelayBudgetReport__root__Type, DelayBudgetReport__root__cond z -> DelayBudgetReport__root__type1__cond (DelayBudgetReport__root__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition DelayBudgetReport__root__helper3 : (forall z : DelayBudgetReport__root__Type, DelayBudgetReport__root__F2 (DelayBudgetReport__root__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition DelayBudgetReport__root__helper4 : (forall y : DelayBudgetReport__root__type1__Type, DelayBudgetReport__root__type1__cond y -> DelayBudgetReport__root__cond (DelayBudgetReport__root__F2 y) /\  DelayBudgetReport__root__F1 (DelayBudgetReport__root__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition DelayBudgetReport__root__Format : T_Format DelayBudgetReport__root__Type DelayBudgetReport__root__cond :=
  proj2_format DelayBudgetReport__root__cond DelayBudgetReport__root__type1__Format DelayBudgetReport__root__F1 DelayBudgetReport__root__F2 DelayBudgetReport__root__helper2 DelayBudgetReport__root__helper3 DelayBudgetReport__root__helper4.
Opaque DelayBudgetReport__root__cond DelayBudgetReport__root__Format.

Definition DelayBudgetReport__ext__Format : T_Format DelayBudgetReport__ext__Type DelayBudgetReport__ext__cond := empty_format.
Opaque DelayBudgetReport__ext__cond DelayBudgetReport__ext__Format.

Definition DelayBudgetReport__Format : T_Format DelayBudgetReport__Type DelayBudgetReport__cond := sum_format DelayBudgetReport__root__Format DelayBudgetReport__ext__Format.
Opaque DelayBudgetReport__cond DelayBudgetReport__Format.

