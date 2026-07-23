Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive EUTRA_Q_OffsetRange__Type : Set :=
 | EUTRA_Q_OffsetRange__dB_24
 | EUTRA_Q_OffsetRange__dB_22
 | EUTRA_Q_OffsetRange__dB_20
 | EUTRA_Q_OffsetRange__dB_18
 | EUTRA_Q_OffsetRange__dB_16
 | EUTRA_Q_OffsetRange__dB_14
 | EUTRA_Q_OffsetRange__dB_12
 | EUTRA_Q_OffsetRange__dB_10
 | EUTRA_Q_OffsetRange__dB_8
 | EUTRA_Q_OffsetRange__dB_6
 | EUTRA_Q_OffsetRange__dB_5
 | EUTRA_Q_OffsetRange__dB_4
 | EUTRA_Q_OffsetRange__dB_3
 | EUTRA_Q_OffsetRange__dB_2
 | EUTRA_Q_OffsetRange__dB_1
 | EUTRA_Q_OffsetRange__dB0
 | EUTRA_Q_OffsetRange__dB1
 | EUTRA_Q_OffsetRange__dB2
 | EUTRA_Q_OffsetRange__dB3
 | EUTRA_Q_OffsetRange__dB4
 | EUTRA_Q_OffsetRange__dB5
 | EUTRA_Q_OffsetRange__dB6
 | EUTRA_Q_OffsetRange__dB8
 | EUTRA_Q_OffsetRange__dB10
 | EUTRA_Q_OffsetRange__dB12
 | EUTRA_Q_OffsetRange__dB14
 | EUTRA_Q_OffsetRange__dB16
 | EUTRA_Q_OffsetRange__dB18
 | EUTRA_Q_OffsetRange__dB20
 | EUTRA_Q_OffsetRange__dB22
 | EUTRA_Q_OffsetRange__dB24
.
Definition EUTRA_Q_OffsetRange__cond := (fun (_ : EUTRA_Q_OffsetRange__Type) => True).
Lemma EUTRA_Q_OffsetRange__nat__helper : to_bit_sz 30 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_Q_OffsetRange__nat__Format : T_Format nat (fun z => (z <= 30)) :=
  nat_enum_format 30 EUTRA_Q_OffsetRange__nat__helper.

Definition EUTRA_Q_OffsetRange__F1 t :=
  match t with
  | EUTRA_Q_OffsetRange__dB_24 => 0
  | EUTRA_Q_OffsetRange__dB_22 => 1
  | EUTRA_Q_OffsetRange__dB_20 => 2
  | EUTRA_Q_OffsetRange__dB_18 => 3
  | EUTRA_Q_OffsetRange__dB_16 => 4
  | EUTRA_Q_OffsetRange__dB_14 => 5
  | EUTRA_Q_OffsetRange__dB_12 => 6
  | EUTRA_Q_OffsetRange__dB_10 => 7
  | EUTRA_Q_OffsetRange__dB_8 => 8
  | EUTRA_Q_OffsetRange__dB_6 => 9
  | EUTRA_Q_OffsetRange__dB_5 => 10
  | EUTRA_Q_OffsetRange__dB_4 => 11
  | EUTRA_Q_OffsetRange__dB_3 => 12
  | EUTRA_Q_OffsetRange__dB_2 => 13
  | EUTRA_Q_OffsetRange__dB_1 => 14
  | EUTRA_Q_OffsetRange__dB0 => 15
  | EUTRA_Q_OffsetRange__dB1 => 16
  | EUTRA_Q_OffsetRange__dB2 => 17
  | EUTRA_Q_OffsetRange__dB3 => 18
  | EUTRA_Q_OffsetRange__dB4 => 19
  | EUTRA_Q_OffsetRange__dB5 => 20
  | EUTRA_Q_OffsetRange__dB6 => 21
  | EUTRA_Q_OffsetRange__dB8 => 22
  | EUTRA_Q_OffsetRange__dB10 => 23
  | EUTRA_Q_OffsetRange__dB12 => 24
  | EUTRA_Q_OffsetRange__dB14 => 25
  | EUTRA_Q_OffsetRange__dB16 => 26
  | EUTRA_Q_OffsetRange__dB18 => 27
  | EUTRA_Q_OffsetRange__dB20 => 28
  | EUTRA_Q_OffsetRange__dB22 => 29
  | EUTRA_Q_OffsetRange__dB24 => 30
  end.
Definition EUTRA_Q_OffsetRange__F2 n :=
  match n with
  | 0 => EUTRA_Q_OffsetRange__dB_24
  | 1 => EUTRA_Q_OffsetRange__dB_22
  | 2 => EUTRA_Q_OffsetRange__dB_20
  | 3 => EUTRA_Q_OffsetRange__dB_18
  | 4 => EUTRA_Q_OffsetRange__dB_16
  | 5 => EUTRA_Q_OffsetRange__dB_14
  | 6 => EUTRA_Q_OffsetRange__dB_12
  | 7 => EUTRA_Q_OffsetRange__dB_10
  | 8 => EUTRA_Q_OffsetRange__dB_8
  | 9 => EUTRA_Q_OffsetRange__dB_6
  | 10 => EUTRA_Q_OffsetRange__dB_5
  | 11 => EUTRA_Q_OffsetRange__dB_4
  | 12 => EUTRA_Q_OffsetRange__dB_3
  | 13 => EUTRA_Q_OffsetRange__dB_2
  | 14 => EUTRA_Q_OffsetRange__dB_1
  | 15 => EUTRA_Q_OffsetRange__dB0
  | 16 => EUTRA_Q_OffsetRange__dB1
  | 17 => EUTRA_Q_OffsetRange__dB2
  | 18 => EUTRA_Q_OffsetRange__dB3
  | 19 => EUTRA_Q_OffsetRange__dB4
  | 20 => EUTRA_Q_OffsetRange__dB5
  | 21 => EUTRA_Q_OffsetRange__dB6
  | 22 => EUTRA_Q_OffsetRange__dB8
  | 23 => EUTRA_Q_OffsetRange__dB10
  | 24 => EUTRA_Q_OffsetRange__dB12
  | 25 => EUTRA_Q_OffsetRange__dB14
  | 26 => EUTRA_Q_OffsetRange__dB16
  | 27 => EUTRA_Q_OffsetRange__dB18
  | 28 => EUTRA_Q_OffsetRange__dB20
  | 29 => EUTRA_Q_OffsetRange__dB22
  | 30 => EUTRA_Q_OffsetRange__dB24
  | _ => EUTRA_Q_OffsetRange__dB_24
  end.
Lemma EUTRA_Q_OffsetRange__F1F2 : forall x : EUTRA_Q_OffsetRange__Type, (EUTRA_Q_OffsetRange__F1 x <= 30) /\ EUTRA_Q_OffsetRange__F2 (EUTRA_Q_OffsetRange__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_Q_OffsetRange__F2F1 : forall (y : nat) (H : y <= 30), EUTRA_Q_OffsetRange__F1 (EUTRA_Q_OffsetRange__F2 y) = y. enum_solve H y. Qed.


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
Definition EUTRA_Q_OffsetRange__Format : T_Format EUTRA_Q_OffsetRange__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_Q_OffsetRange__nat__Format EUTRA_Q_OffsetRange__F1 EUTRA_Q_OffsetRange__F2 EUTRA_Q_OffsetRange__F1F2 EUTRA_Q_OffsetRange__F2F1.

Opaque EUTRA_Q_OffsetRange__cond EUTRA_Q_OffsetRange__Format.

