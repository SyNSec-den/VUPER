Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Inductive SL_SIB_ReqInfo_r17__root__Type : Set :=
 | SL_SIB_ReqInfo_r17__root__sib1
 | SL_SIB_ReqInfo_r17__root__sib2
 | SL_SIB_ReqInfo_r17__root__sib3
 | SL_SIB_ReqInfo_r17__root__sib4
 | SL_SIB_ReqInfo_r17__root__sib5
 | SL_SIB_ReqInfo_r17__root__sib6
 | SL_SIB_ReqInfo_r17__root__sib7
 | SL_SIB_ReqInfo_r17__root__sib8
 | SL_SIB_ReqInfo_r17__root__sib9
 | SL_SIB_ReqInfo_r17__root__sib10
 | SL_SIB_ReqInfo_r17__root__sib11
 | SL_SIB_ReqInfo_r17__root__sib12
 | SL_SIB_ReqInfo_r17__root__sib13
 | SL_SIB_ReqInfo_r17__root__sib14
 | SL_SIB_ReqInfo_r17__root__sib15
 | SL_SIB_ReqInfo_r17__root__sib16
 | SL_SIB_ReqInfo_r17__root__sib17
 | SL_SIB_ReqInfo_r17__root__sib18
 | SL_SIB_ReqInfo_r17__root__sib19
 | SL_SIB_ReqInfo_r17__root__sib20
 | SL_SIB_ReqInfo_r17__root__sib21
 | SL_SIB_ReqInfo_r17__root__spare11
 | SL_SIB_ReqInfo_r17__root__spare10
 | SL_SIB_ReqInfo_r17__root__spare9
 | SL_SIB_ReqInfo_r17__root__spare8
 | SL_SIB_ReqInfo_r17__root__spare7
 | SL_SIB_ReqInfo_r17__root__spare6
 | SL_SIB_ReqInfo_r17__root__spare5
 | SL_SIB_ReqInfo_r17__root__spare4
 | SL_SIB_ReqInfo_r17__root__spare3
 | SL_SIB_ReqInfo_r17__root__spare2
 | SL_SIB_ReqInfo_r17__root__spare1
.
Definition SL_SIB_ReqInfo_r17__root__cond := (fun (_ : SL_SIB_ReqInfo_r17__root__Type) => True).
Lemma SL_SIB_ReqInfo_r17__root__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_SIB_ReqInfo_r17__root__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_SIB_ReqInfo_r17__root__nat__helper.

Definition SL_SIB_ReqInfo_r17__root__F1 t :=
  match t with
  | SL_SIB_ReqInfo_r17__root__sib1 => 0
  | SL_SIB_ReqInfo_r17__root__sib2 => 1
  | SL_SIB_ReqInfo_r17__root__sib3 => 2
  | SL_SIB_ReqInfo_r17__root__sib4 => 3
  | SL_SIB_ReqInfo_r17__root__sib5 => 4
  | SL_SIB_ReqInfo_r17__root__sib6 => 5
  | SL_SIB_ReqInfo_r17__root__sib7 => 6
  | SL_SIB_ReqInfo_r17__root__sib8 => 7
  | SL_SIB_ReqInfo_r17__root__sib9 => 8
  | SL_SIB_ReqInfo_r17__root__sib10 => 9
  | SL_SIB_ReqInfo_r17__root__sib11 => 10
  | SL_SIB_ReqInfo_r17__root__sib12 => 11
  | SL_SIB_ReqInfo_r17__root__sib13 => 12
  | SL_SIB_ReqInfo_r17__root__sib14 => 13
  | SL_SIB_ReqInfo_r17__root__sib15 => 14
  | SL_SIB_ReqInfo_r17__root__sib16 => 15
  | SL_SIB_ReqInfo_r17__root__sib17 => 16
  | SL_SIB_ReqInfo_r17__root__sib18 => 17
  | SL_SIB_ReqInfo_r17__root__sib19 => 18
  | SL_SIB_ReqInfo_r17__root__sib20 => 19
  | SL_SIB_ReqInfo_r17__root__sib21 => 20
  | SL_SIB_ReqInfo_r17__root__spare11 => 21
  | SL_SIB_ReqInfo_r17__root__spare10 => 22
  | SL_SIB_ReqInfo_r17__root__spare9 => 23
  | SL_SIB_ReqInfo_r17__root__spare8 => 24
  | SL_SIB_ReqInfo_r17__root__spare7 => 25
  | SL_SIB_ReqInfo_r17__root__spare6 => 26
  | SL_SIB_ReqInfo_r17__root__spare5 => 27
  | SL_SIB_ReqInfo_r17__root__spare4 => 28
  | SL_SIB_ReqInfo_r17__root__spare3 => 29
  | SL_SIB_ReqInfo_r17__root__spare2 => 30
  | SL_SIB_ReqInfo_r17__root__spare1 => 31
  end.
Definition SL_SIB_ReqInfo_r17__root__F2 n :=
  match n with
  | 0 => SL_SIB_ReqInfo_r17__root__sib1
  | 1 => SL_SIB_ReqInfo_r17__root__sib2
  | 2 => SL_SIB_ReqInfo_r17__root__sib3
  | 3 => SL_SIB_ReqInfo_r17__root__sib4
  | 4 => SL_SIB_ReqInfo_r17__root__sib5
  | 5 => SL_SIB_ReqInfo_r17__root__sib6
  | 6 => SL_SIB_ReqInfo_r17__root__sib7
  | 7 => SL_SIB_ReqInfo_r17__root__sib8
  | 8 => SL_SIB_ReqInfo_r17__root__sib9
  | 9 => SL_SIB_ReqInfo_r17__root__sib10
  | 10 => SL_SIB_ReqInfo_r17__root__sib11
  | 11 => SL_SIB_ReqInfo_r17__root__sib12
  | 12 => SL_SIB_ReqInfo_r17__root__sib13
  | 13 => SL_SIB_ReqInfo_r17__root__sib14
  | 14 => SL_SIB_ReqInfo_r17__root__sib15
  | 15 => SL_SIB_ReqInfo_r17__root__sib16
  | 16 => SL_SIB_ReqInfo_r17__root__sib17
  | 17 => SL_SIB_ReqInfo_r17__root__sib18
  | 18 => SL_SIB_ReqInfo_r17__root__sib19
  | 19 => SL_SIB_ReqInfo_r17__root__sib20
  | 20 => SL_SIB_ReqInfo_r17__root__sib21
  | 21 => SL_SIB_ReqInfo_r17__root__spare11
  | 22 => SL_SIB_ReqInfo_r17__root__spare10
  | 23 => SL_SIB_ReqInfo_r17__root__spare9
  | 24 => SL_SIB_ReqInfo_r17__root__spare8
  | 25 => SL_SIB_ReqInfo_r17__root__spare7
  | 26 => SL_SIB_ReqInfo_r17__root__spare6
  | 27 => SL_SIB_ReqInfo_r17__root__spare5
  | 28 => SL_SIB_ReqInfo_r17__root__spare4
  | 29 => SL_SIB_ReqInfo_r17__root__spare3
  | 30 => SL_SIB_ReqInfo_r17__root__spare2
  | 31 => SL_SIB_ReqInfo_r17__root__spare1
  | _ => SL_SIB_ReqInfo_r17__root__sib1
  end.
Lemma SL_SIB_ReqInfo_r17__root__F1F2 : forall x : SL_SIB_ReqInfo_r17__root__Type, (SL_SIB_ReqInfo_r17__root__F1 x <= 31) /\ SL_SIB_ReqInfo_r17__root__F2 (SL_SIB_ReqInfo_r17__root__F1 x) = x. imp_solve. Qed.
Lemma SL_SIB_ReqInfo_r17__root__F2F1 : forall (y : nat) (H : y <= 31), SL_SIB_ReqInfo_r17__root__F1 (SL_SIB_ReqInfo_r17__root__F2 y) = y. enum_solve H y. Qed.

Definition SL_SIB_ReqInfo_r17__ext__Type : Set := Empty_set.
Definition SL_SIB_ReqInfo_r17__ext__cond := (fun (_ : SL_SIB_ReqInfo_r17__ext__Type) => True).
Definition SL_SIB_ReqInfo_r17__Type : Set := SL_SIB_ReqInfo_r17__root__Type + SL_SIB_ReqInfo_r17__ext__Type.
Definition SL_SIB_ReqInfo_r17__cond := sum_cond SL_SIB_ReqInfo_r17__root__cond SL_SIB_ReqInfo_r17__ext__cond.


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
Definition SL_SIB_ReqInfo_r17__root__Format : T_Format SL_SIB_ReqInfo_r17__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format SL_SIB_ReqInfo_r17__root__nat__Format SL_SIB_ReqInfo_r17__root__F1 SL_SIB_ReqInfo_r17__root__F2 SL_SIB_ReqInfo_r17__root__F1F2 SL_SIB_ReqInfo_r17__root__F2F1.

Opaque SL_SIB_ReqInfo_r17__root__cond SL_SIB_ReqInfo_r17__root__Format.

Definition SL_SIB_ReqInfo_r17__ext__Format : T_Format SL_SIB_ReqInfo_r17__ext__Type SL_SIB_ReqInfo_r17__ext__cond := empty_format.

Opaque SL_SIB_ReqInfo_r17__ext__cond SL_SIB_ReqInfo_r17__ext__Format.

Definition SL_SIB_ReqInfo_r17__Format : T_Format SL_SIB_ReqInfo_r17__Type SL_SIB_ReqInfo_r17__cond := sum_format SL_SIB_ReqInfo_r17__root__Format SL_SIB_ReqInfo_r17__ext__Format.
Opaque SL_SIB_ReqInfo_r17__cond SL_SIB_ReqInfo_r17__Format.

Opaque SL_SIB_ReqInfo_r17__cond SL_SIB_ReqInfo_r17__Format.

