Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive IntegrityProtAlgorithm__root__Type : Set :=
 | IntegrityProtAlgorithm__root__nia0
 | IntegrityProtAlgorithm__root__nia1
 | IntegrityProtAlgorithm__root__nia2
 | IntegrityProtAlgorithm__root__nia3
 | IntegrityProtAlgorithm__root__spare4
 | IntegrityProtAlgorithm__root__spare3
 | IntegrityProtAlgorithm__root__spare2
 | IntegrityProtAlgorithm__root__spare1
.
Definition IntegrityProtAlgorithm__root__cond := (fun (_ : IntegrityProtAlgorithm__root__Type) => True).
Lemma IntegrityProtAlgorithm__root__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition IntegrityProtAlgorithm__root__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 IntegrityProtAlgorithm__root__nat__helper.

Definition IntegrityProtAlgorithm__root__F1 t :=
  match t with
  | IntegrityProtAlgorithm__root__nia0 => 0
  | IntegrityProtAlgorithm__root__nia1 => 1
  | IntegrityProtAlgorithm__root__nia2 => 2
  | IntegrityProtAlgorithm__root__nia3 => 3
  | IntegrityProtAlgorithm__root__spare4 => 4
  | IntegrityProtAlgorithm__root__spare3 => 5
  | IntegrityProtAlgorithm__root__spare2 => 6
  | IntegrityProtAlgorithm__root__spare1 => 7
  end.
Definition IntegrityProtAlgorithm__root__F2 n :=
  match n with
  | 0 => IntegrityProtAlgorithm__root__nia0
  | 1 => IntegrityProtAlgorithm__root__nia1
  | 2 => IntegrityProtAlgorithm__root__nia2
  | 3 => IntegrityProtAlgorithm__root__nia3
  | 4 => IntegrityProtAlgorithm__root__spare4
  | 5 => IntegrityProtAlgorithm__root__spare3
  | 6 => IntegrityProtAlgorithm__root__spare2
  | 7 => IntegrityProtAlgorithm__root__spare1
  | _ => IntegrityProtAlgorithm__root__nia0
  end.
Lemma IntegrityProtAlgorithm__root__F1F2 : forall x : IntegrityProtAlgorithm__root__Type, (IntegrityProtAlgorithm__root__F1 x <= 7) /\ IntegrityProtAlgorithm__root__F2 (IntegrityProtAlgorithm__root__F1 x) = x. imp_solve. Qed.
Lemma IntegrityProtAlgorithm__root__F2F1 : forall (y : nat) (H : y <= 7), IntegrityProtAlgorithm__root__F1 (IntegrityProtAlgorithm__root__F2 y) = y. enum_solve H y. Qed.

Definition IntegrityProtAlgorithm__ext__Type : Set := Empty_set.
Definition IntegrityProtAlgorithm__ext__cond := (fun (_ : IntegrityProtAlgorithm__ext__Type) => True).
Definition IntegrityProtAlgorithm__Type : Set := IntegrityProtAlgorithm__root__Type + IntegrityProtAlgorithm__ext__Type.
Definition IntegrityProtAlgorithm__cond := sum_cond IntegrityProtAlgorithm__root__cond IntegrityProtAlgorithm__ext__cond.


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
Definition IntegrityProtAlgorithm__root__Format : T_Format IntegrityProtAlgorithm__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format IntegrityProtAlgorithm__root__nat__Format IntegrityProtAlgorithm__root__F1 IntegrityProtAlgorithm__root__F2 IntegrityProtAlgorithm__root__F1F2 IntegrityProtAlgorithm__root__F2F1.

Opaque IntegrityProtAlgorithm__root__cond IntegrityProtAlgorithm__root__Format.

Definition IntegrityProtAlgorithm__ext__Format : T_Format IntegrityProtAlgorithm__ext__Type IntegrityProtAlgorithm__ext__cond := empty_format.

Opaque IntegrityProtAlgorithm__ext__cond IntegrityProtAlgorithm__ext__Format.

Definition IntegrityProtAlgorithm__Format : T_Format IntegrityProtAlgorithm__Type IntegrityProtAlgorithm__cond := sum_format IntegrityProtAlgorithm__root__Format IntegrityProtAlgorithm__ext__Format.
Opaque IntegrityProtAlgorithm__cond IntegrityProtAlgorithm__Format.

Opaque IntegrityProtAlgorithm__cond IntegrityProtAlgorithm__Format.

