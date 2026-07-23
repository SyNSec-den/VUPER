Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ReportInterval__Type : Set :=
 | ReportInterval__ms120
 | ReportInterval__ms240
 | ReportInterval__ms480
 | ReportInterval__ms640
 | ReportInterval__ms1024
 | ReportInterval__ms2048
 | ReportInterval__ms5120
 | ReportInterval__ms10240
 | ReportInterval__ms20480
 | ReportInterval__ms40960
 | ReportInterval__min1
 | ReportInterval__min6
 | ReportInterval__min12
 | ReportInterval__min30
.
Definition ReportInterval__cond := (fun (_ : ReportInterval__Type) => True).
Lemma ReportInterval__nat__helper : to_bit_sz 13 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReportInterval__nat__Format : T_Format nat (fun z => (z <= 13)) :=
  nat_enum_format 13 ReportInterval__nat__helper.

Definition ReportInterval__F1 t :=
  match t with
  | ReportInterval__ms120 => 0
  | ReportInterval__ms240 => 1
  | ReportInterval__ms480 => 2
  | ReportInterval__ms640 => 3
  | ReportInterval__ms1024 => 4
  | ReportInterval__ms2048 => 5
  | ReportInterval__ms5120 => 6
  | ReportInterval__ms10240 => 7
  | ReportInterval__ms20480 => 8
  | ReportInterval__ms40960 => 9
  | ReportInterval__min1 => 10
  | ReportInterval__min6 => 11
  | ReportInterval__min12 => 12
  | ReportInterval__min30 => 13
  end.
Definition ReportInterval__F2 n :=
  match n with
  | 0 => ReportInterval__ms120
  | 1 => ReportInterval__ms240
  | 2 => ReportInterval__ms480
  | 3 => ReportInterval__ms640
  | 4 => ReportInterval__ms1024
  | 5 => ReportInterval__ms2048
  | 6 => ReportInterval__ms5120
  | 7 => ReportInterval__ms10240
  | 8 => ReportInterval__ms20480
  | 9 => ReportInterval__ms40960
  | 10 => ReportInterval__min1
  | 11 => ReportInterval__min6
  | 12 => ReportInterval__min12
  | 13 => ReportInterval__min30
  | _ => ReportInterval__ms120
  end.
Lemma ReportInterval__F1F2 : forall x : ReportInterval__Type, (ReportInterval__F1 x <= 13) /\ ReportInterval__F2 (ReportInterval__F1 x) = x. imp_solve. Qed.
Lemma ReportInterval__F2F1 : forall (y : nat) (H : y <= 13), ReportInterval__F1 (ReportInterval__F2 y) = y. enum_solve H y. Qed.


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
Definition ReportInterval__Format : T_Format ReportInterval__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReportInterval__nat__Format ReportInterval__F1 ReportInterval__F2 ReportInterval__F1F2 ReportInterval__F2F1.

Opaque ReportInterval__cond ReportInterval__Format.

