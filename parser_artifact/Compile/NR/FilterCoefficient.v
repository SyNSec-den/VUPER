Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FilterCoefficient__root__Type : Set :=
 | FilterCoefficient__root__fc0
 | FilterCoefficient__root__fc1
 | FilterCoefficient__root__fc2
 | FilterCoefficient__root__fc3
 | FilterCoefficient__root__fc4
 | FilterCoefficient__root__fc5
 | FilterCoefficient__root__fc6
 | FilterCoefficient__root__fc7
 | FilterCoefficient__root__fc8
 | FilterCoefficient__root__fc9
 | FilterCoefficient__root__fc11
 | FilterCoefficient__root__fc13
 | FilterCoefficient__root__fc15
 | FilterCoefficient__root__fc17
 | FilterCoefficient__root__fc19
 | FilterCoefficient__root__spare1
.
Definition FilterCoefficient__root__cond := (fun (_ : FilterCoefficient__root__Type) => True).
Lemma FilterCoefficient__root__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FilterCoefficient__root__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 FilterCoefficient__root__nat__helper.

Definition FilterCoefficient__root__F1 t :=
  match t with
  | FilterCoefficient__root__fc0 => 0
  | FilterCoefficient__root__fc1 => 1
  | FilterCoefficient__root__fc2 => 2
  | FilterCoefficient__root__fc3 => 3
  | FilterCoefficient__root__fc4 => 4
  | FilterCoefficient__root__fc5 => 5
  | FilterCoefficient__root__fc6 => 6
  | FilterCoefficient__root__fc7 => 7
  | FilterCoefficient__root__fc8 => 8
  | FilterCoefficient__root__fc9 => 9
  | FilterCoefficient__root__fc11 => 10
  | FilterCoefficient__root__fc13 => 11
  | FilterCoefficient__root__fc15 => 12
  | FilterCoefficient__root__fc17 => 13
  | FilterCoefficient__root__fc19 => 14
  | FilterCoefficient__root__spare1 => 15
  end.
Definition FilterCoefficient__root__F2 n :=
  match n with
  | 0 => FilterCoefficient__root__fc0
  | 1 => FilterCoefficient__root__fc1
  | 2 => FilterCoefficient__root__fc2
  | 3 => FilterCoefficient__root__fc3
  | 4 => FilterCoefficient__root__fc4
  | 5 => FilterCoefficient__root__fc5
  | 6 => FilterCoefficient__root__fc6
  | 7 => FilterCoefficient__root__fc7
  | 8 => FilterCoefficient__root__fc8
  | 9 => FilterCoefficient__root__fc9
  | 10 => FilterCoefficient__root__fc11
  | 11 => FilterCoefficient__root__fc13
  | 12 => FilterCoefficient__root__fc15
  | 13 => FilterCoefficient__root__fc17
  | 14 => FilterCoefficient__root__fc19
  | 15 => FilterCoefficient__root__spare1
  | _ => FilterCoefficient__root__fc0
  end.
Lemma FilterCoefficient__root__F1F2 : forall x : FilterCoefficient__root__Type, (FilterCoefficient__root__F1 x <= 15) /\ FilterCoefficient__root__F2 (FilterCoefficient__root__F1 x) = x. imp_solve. Qed.
Lemma FilterCoefficient__root__F2F1 : forall (y : nat) (H : y <= 15), FilterCoefficient__root__F1 (FilterCoefficient__root__F2 y) = y. enum_solve H y. Qed.

Definition FilterCoefficient__ext__Type : Set := Empty_set.
Definition FilterCoefficient__ext__cond := (fun (_ : FilterCoefficient__ext__Type) => True).
Definition FilterCoefficient__Type : Set := FilterCoefficient__root__Type + FilterCoefficient__ext__Type.
Definition FilterCoefficient__cond := sum_cond FilterCoefficient__root__cond FilterCoefficient__ext__cond.


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
Definition FilterCoefficient__root__Format : T_Format FilterCoefficient__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format FilterCoefficient__root__nat__Format FilterCoefficient__root__F1 FilterCoefficient__root__F2 FilterCoefficient__root__F1F2 FilterCoefficient__root__F2F1.

Opaque FilterCoefficient__root__cond FilterCoefficient__root__Format.

Definition FilterCoefficient__ext__Format : T_Format FilterCoefficient__ext__Type FilterCoefficient__ext__cond := empty_format.

Opaque FilterCoefficient__ext__cond FilterCoefficient__ext__Format.

Definition FilterCoefficient__Format : T_Format FilterCoefficient__Type FilterCoefficient__cond := sum_format FilterCoefficient__root__Format FilterCoefficient__ext__Format.
Opaque FilterCoefficient__cond FilterCoefficient__Format.

Opaque FilterCoefficient__cond FilterCoefficient__Format.

