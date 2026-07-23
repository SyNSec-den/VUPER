Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive AccessStratumRelease__root__Type : Set :=
 | AccessStratumRelease__root__rel15
 | AccessStratumRelease__root__rel16
 | AccessStratumRelease__root__rel17
 | AccessStratumRelease__root__spare5
 | AccessStratumRelease__root__spare4
 | AccessStratumRelease__root__spare3
 | AccessStratumRelease__root__spare2
 | AccessStratumRelease__root__spare1
.
Definition AccessStratumRelease__root__cond := (fun (_ : AccessStratumRelease__root__Type) => True).
Lemma AccessStratumRelease__root__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition AccessStratumRelease__root__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 AccessStratumRelease__root__nat__helper.

Definition AccessStratumRelease__root__F1 t :=
  match t with
  | AccessStratumRelease__root__rel15 => 0
  | AccessStratumRelease__root__rel16 => 1
  | AccessStratumRelease__root__rel17 => 2
  | AccessStratumRelease__root__spare5 => 3
  | AccessStratumRelease__root__spare4 => 4
  | AccessStratumRelease__root__spare3 => 5
  | AccessStratumRelease__root__spare2 => 6
  | AccessStratumRelease__root__spare1 => 7
  end.
Definition AccessStratumRelease__root__F2 n :=
  match n with
  | 0 => AccessStratumRelease__root__rel15
  | 1 => AccessStratumRelease__root__rel16
  | 2 => AccessStratumRelease__root__rel17
  | 3 => AccessStratumRelease__root__spare5
  | 4 => AccessStratumRelease__root__spare4
  | 5 => AccessStratumRelease__root__spare3
  | 6 => AccessStratumRelease__root__spare2
  | 7 => AccessStratumRelease__root__spare1
  | _ => AccessStratumRelease__root__rel15
  end.
Lemma AccessStratumRelease__root__F1F2 : forall x : AccessStratumRelease__root__Type, (AccessStratumRelease__root__F1 x <= 7) /\ AccessStratumRelease__root__F2 (AccessStratumRelease__root__F1 x) = x. imp_solve. Qed.
Lemma AccessStratumRelease__root__F2F1 : forall (y : nat) (H : y <= 7), AccessStratumRelease__root__F1 (AccessStratumRelease__root__F2 y) = y. enum_solve H y. Qed.

Definition AccessStratumRelease__ext__Type : Set := Empty_set.
Definition AccessStratumRelease__ext__cond := (fun (_ : AccessStratumRelease__ext__Type) => True).
Definition AccessStratumRelease__Type : Set := AccessStratumRelease__root__Type + AccessStratumRelease__ext__Type.
Definition AccessStratumRelease__cond := sum_cond AccessStratumRelease__root__cond AccessStratumRelease__ext__cond.


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
Definition AccessStratumRelease__root__Format : T_Format AccessStratumRelease__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format AccessStratumRelease__root__nat__Format AccessStratumRelease__root__F1 AccessStratumRelease__root__F2 AccessStratumRelease__root__F1F2 AccessStratumRelease__root__F2F1.

Opaque AccessStratumRelease__root__cond AccessStratumRelease__root__Format.

Definition AccessStratumRelease__ext__Format : T_Format AccessStratumRelease__ext__Type AccessStratumRelease__ext__cond := empty_format.

Opaque AccessStratumRelease__ext__cond AccessStratumRelease__ext__Format.

Definition AccessStratumRelease__Format : T_Format AccessStratumRelease__Type AccessStratumRelease__cond := sum_format AccessStratumRelease__root__Format AccessStratumRelease__ext__Format.
Opaque AccessStratumRelease__cond AccessStratumRelease__Format.

Opaque AccessStratumRelease__cond AccessStratumRelease__Format.

