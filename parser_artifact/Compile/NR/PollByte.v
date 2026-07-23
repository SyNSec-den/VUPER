Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PollByte__Type : Set :=
 | PollByte__kB1
 | PollByte__kB2
 | PollByte__kB5
 | PollByte__kB8
 | PollByte__kB10
 | PollByte__kB15
 | PollByte__kB25
 | PollByte__kB50
 | PollByte__kB75
 | PollByte__kB100
 | PollByte__kB125
 | PollByte__kB250
 | PollByte__kB375
 | PollByte__kB500
 | PollByte__kB750
 | PollByte__kB1000
 | PollByte__kB1250
 | PollByte__kB1500
 | PollByte__kB2000
 | PollByte__kB3000
 | PollByte__kB4000
 | PollByte__kB4500
 | PollByte__kB5000
 | PollByte__kB5500
 | PollByte__kB6000
 | PollByte__kB6500
 | PollByte__kB7000
 | PollByte__kB7500
 | PollByte__mB8
 | PollByte__mB9
 | PollByte__mB10
 | PollByte__mB11
 | PollByte__mB12
 | PollByte__mB13
 | PollByte__mB14
 | PollByte__mB15
 | PollByte__mB16
 | PollByte__mB17
 | PollByte__mB18
 | PollByte__mB20
 | PollByte__mB25
 | PollByte__mB30
 | PollByte__mB40
 | PollByte__infinity
 | PollByte__spare20
 | PollByte__spare19
 | PollByte__spare18
 | PollByte__spare17
 | PollByte__spare16
 | PollByte__spare15
 | PollByte__spare14
 | PollByte__spare13
 | PollByte__spare12
 | PollByte__spare11
 | PollByte__spare10
 | PollByte__spare9
 | PollByte__spare8
 | PollByte__spare7
 | PollByte__spare6
 | PollByte__spare5
 | PollByte__spare4
 | PollByte__spare3
 | PollByte__spare2
 | PollByte__spare1
.
Definition PollByte__cond := (fun (_ : PollByte__Type) => True).
Lemma PollByte__nat__helper : to_bit_sz 63 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PollByte__nat__Format : T_Format nat (fun z => (z <= 63)) :=
  nat_enum_format 63 PollByte__nat__helper.

Definition PollByte__F1 t :=
  match t with
  | PollByte__kB1 => 0
  | PollByte__kB2 => 1
  | PollByte__kB5 => 2
  | PollByte__kB8 => 3
  | PollByte__kB10 => 4
  | PollByte__kB15 => 5
  | PollByte__kB25 => 6
  | PollByte__kB50 => 7
  | PollByte__kB75 => 8
  | PollByte__kB100 => 9
  | PollByte__kB125 => 10
  | PollByte__kB250 => 11
  | PollByte__kB375 => 12
  | PollByte__kB500 => 13
  | PollByte__kB750 => 14
  | PollByte__kB1000 => 15
  | PollByte__kB1250 => 16
  | PollByte__kB1500 => 17
  | PollByte__kB2000 => 18
  | PollByte__kB3000 => 19
  | PollByte__kB4000 => 20
  | PollByte__kB4500 => 21
  | PollByte__kB5000 => 22
  | PollByte__kB5500 => 23
  | PollByte__kB6000 => 24
  | PollByte__kB6500 => 25
  | PollByte__kB7000 => 26
  | PollByte__kB7500 => 27
  | PollByte__mB8 => 28
  | PollByte__mB9 => 29
  | PollByte__mB10 => 30
  | PollByte__mB11 => 31
  | PollByte__mB12 => 32
  | PollByte__mB13 => 33
  | PollByte__mB14 => 34
  | PollByte__mB15 => 35
  | PollByte__mB16 => 36
  | PollByte__mB17 => 37
  | PollByte__mB18 => 38
  | PollByte__mB20 => 39
  | PollByte__mB25 => 40
  | PollByte__mB30 => 41
  | PollByte__mB40 => 42
  | PollByte__infinity => 43
  | PollByte__spare20 => 44
  | PollByte__spare19 => 45
  | PollByte__spare18 => 46
  | PollByte__spare17 => 47
  | PollByte__spare16 => 48
  | PollByte__spare15 => 49
  | PollByte__spare14 => 50
  | PollByte__spare13 => 51
  | PollByte__spare12 => 52
  | PollByte__spare11 => 53
  | PollByte__spare10 => 54
  | PollByte__spare9 => 55
  | PollByte__spare8 => 56
  | PollByte__spare7 => 57
  | PollByte__spare6 => 58
  | PollByte__spare5 => 59
  | PollByte__spare4 => 60
  | PollByte__spare3 => 61
  | PollByte__spare2 => 62
  | PollByte__spare1 => 63
  end.
Definition PollByte__F2 n :=
  match n with
  | 0 => PollByte__kB1
  | 1 => PollByte__kB2
  | 2 => PollByte__kB5
  | 3 => PollByte__kB8
  | 4 => PollByte__kB10
  | 5 => PollByte__kB15
  | 6 => PollByte__kB25
  | 7 => PollByte__kB50
  | 8 => PollByte__kB75
  | 9 => PollByte__kB100
  | 10 => PollByte__kB125
  | 11 => PollByte__kB250
  | 12 => PollByte__kB375
  | 13 => PollByte__kB500
  | 14 => PollByte__kB750
  | 15 => PollByte__kB1000
  | 16 => PollByte__kB1250
  | 17 => PollByte__kB1500
  | 18 => PollByte__kB2000
  | 19 => PollByte__kB3000
  | 20 => PollByte__kB4000
  | 21 => PollByte__kB4500
  | 22 => PollByte__kB5000
  | 23 => PollByte__kB5500
  | 24 => PollByte__kB6000
  | 25 => PollByte__kB6500
  | 26 => PollByte__kB7000
  | 27 => PollByte__kB7500
  | 28 => PollByte__mB8
  | 29 => PollByte__mB9
  | 30 => PollByte__mB10
  | 31 => PollByte__mB11
  | 32 => PollByte__mB12
  | 33 => PollByte__mB13
  | 34 => PollByte__mB14
  | 35 => PollByte__mB15
  | 36 => PollByte__mB16
  | 37 => PollByte__mB17
  | 38 => PollByte__mB18
  | 39 => PollByte__mB20
  | 40 => PollByte__mB25
  | 41 => PollByte__mB30
  | 42 => PollByte__mB40
  | 43 => PollByte__infinity
  | 44 => PollByte__spare20
  | 45 => PollByte__spare19
  | 46 => PollByte__spare18
  | 47 => PollByte__spare17
  | 48 => PollByte__spare16
  | 49 => PollByte__spare15
  | 50 => PollByte__spare14
  | 51 => PollByte__spare13
  | 52 => PollByte__spare12
  | 53 => PollByte__spare11
  | 54 => PollByte__spare10
  | 55 => PollByte__spare9
  | 56 => PollByte__spare8
  | 57 => PollByte__spare7
  | 58 => PollByte__spare6
  | 59 => PollByte__spare5
  | 60 => PollByte__spare4
  | 61 => PollByte__spare3
  | 62 => PollByte__spare2
  | 63 => PollByte__spare1
  | _ => PollByte__kB1
  end.
Lemma PollByte__F1F2 : forall x : PollByte__Type, (PollByte__F1 x <= 63) /\ PollByte__F2 (PollByte__F1 x) = x. imp_solve. Qed.
Lemma PollByte__F2F1 : forall (y : nat) (H : y <= 63), PollByte__F1 (PollByte__F2 y) = y. enum_solve H y. Qed.


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
Definition PollByte__Format : T_Format PollByte__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PollByte__nat__Format PollByte__F1 PollByte__F2 PollByte__F1F2 PollByte__F2F1.

Opaque PollByte__cond PollByte__Format.

