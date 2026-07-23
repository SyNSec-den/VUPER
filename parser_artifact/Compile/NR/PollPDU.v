Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PollPDU__Type : Set :=
 | PollPDU__p4
 | PollPDU__p8
 | PollPDU__p16
 | PollPDU__p32
 | PollPDU__p64
 | PollPDU__p128
 | PollPDU__p256
 | PollPDU__p512
 | PollPDU__p1024
 | PollPDU__p2048
 | PollPDU__p4096
 | PollPDU__p6144
 | PollPDU__p8192
 | PollPDU__p12288
 | PollPDU__p16384
 | PollPDU__p20480
 | PollPDU__p24576
 | PollPDU__p28672
 | PollPDU__p32768
 | PollPDU__p40960
 | PollPDU__p49152
 | PollPDU__p57344
 | PollPDU__p65536
 | PollPDU__infinity
 | PollPDU__spare8
 | PollPDU__spare7
 | PollPDU__spare6
 | PollPDU__spare5
 | PollPDU__spare4
 | PollPDU__spare3
 | PollPDU__spare2
 | PollPDU__spare1
.
Definition PollPDU__cond := (fun (_ : PollPDU__Type) => True).
Lemma PollPDU__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PollPDU__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 PollPDU__nat__helper.

Definition PollPDU__F1 t :=
  match t with
  | PollPDU__p4 => 0
  | PollPDU__p8 => 1
  | PollPDU__p16 => 2
  | PollPDU__p32 => 3
  | PollPDU__p64 => 4
  | PollPDU__p128 => 5
  | PollPDU__p256 => 6
  | PollPDU__p512 => 7
  | PollPDU__p1024 => 8
  | PollPDU__p2048 => 9
  | PollPDU__p4096 => 10
  | PollPDU__p6144 => 11
  | PollPDU__p8192 => 12
  | PollPDU__p12288 => 13
  | PollPDU__p16384 => 14
  | PollPDU__p20480 => 15
  | PollPDU__p24576 => 16
  | PollPDU__p28672 => 17
  | PollPDU__p32768 => 18
  | PollPDU__p40960 => 19
  | PollPDU__p49152 => 20
  | PollPDU__p57344 => 21
  | PollPDU__p65536 => 22
  | PollPDU__infinity => 23
  | PollPDU__spare8 => 24
  | PollPDU__spare7 => 25
  | PollPDU__spare6 => 26
  | PollPDU__spare5 => 27
  | PollPDU__spare4 => 28
  | PollPDU__spare3 => 29
  | PollPDU__spare2 => 30
  | PollPDU__spare1 => 31
  end.
Definition PollPDU__F2 n :=
  match n with
  | 0 => PollPDU__p4
  | 1 => PollPDU__p8
  | 2 => PollPDU__p16
  | 3 => PollPDU__p32
  | 4 => PollPDU__p64
  | 5 => PollPDU__p128
  | 6 => PollPDU__p256
  | 7 => PollPDU__p512
  | 8 => PollPDU__p1024
  | 9 => PollPDU__p2048
  | 10 => PollPDU__p4096
  | 11 => PollPDU__p6144
  | 12 => PollPDU__p8192
  | 13 => PollPDU__p12288
  | 14 => PollPDU__p16384
  | 15 => PollPDU__p20480
  | 16 => PollPDU__p24576
  | 17 => PollPDU__p28672
  | 18 => PollPDU__p32768
  | 19 => PollPDU__p40960
  | 20 => PollPDU__p49152
  | 21 => PollPDU__p57344
  | 22 => PollPDU__p65536
  | 23 => PollPDU__infinity
  | 24 => PollPDU__spare8
  | 25 => PollPDU__spare7
  | 26 => PollPDU__spare6
  | 27 => PollPDU__spare5
  | 28 => PollPDU__spare4
  | 29 => PollPDU__spare3
  | 30 => PollPDU__spare2
  | 31 => PollPDU__spare1
  | _ => PollPDU__p4
  end.
Lemma PollPDU__F1F2 : forall x : PollPDU__Type, (PollPDU__F1 x <= 31) /\ PollPDU__F2 (PollPDU__F1 x) = x. imp_solve. Qed.
Lemma PollPDU__F2F1 : forall (y : nat) (H : y <= 31), PollPDU__F1 (PollPDU__F2 y) = y. enum_solve H y. Qed.


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
Definition PollPDU__Format : T_Format PollPDU__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PollPDU__nat__Format PollPDU__F1 PollPDU__F2 PollPDU__F1F2 PollPDU__F2F1.

Opaque PollPDU__cond PollPDU__Format.

