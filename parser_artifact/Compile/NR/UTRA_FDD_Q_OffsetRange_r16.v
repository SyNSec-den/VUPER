Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UTRA_FDD_Q_OffsetRange_r16__Type : Set :=
 | UTRA_FDD_Q_OffsetRange_r16__dB_24
 | UTRA_FDD_Q_OffsetRange_r16__dB_22
 | UTRA_FDD_Q_OffsetRange_r16__dB_20
 | UTRA_FDD_Q_OffsetRange_r16__dB_18
 | UTRA_FDD_Q_OffsetRange_r16__dB_16
 | UTRA_FDD_Q_OffsetRange_r16__dB_14
 | UTRA_FDD_Q_OffsetRange_r16__dB_12
 | UTRA_FDD_Q_OffsetRange_r16__dB_10
 | UTRA_FDD_Q_OffsetRange_r16__dB_8
 | UTRA_FDD_Q_OffsetRange_r16__dB_6
 | UTRA_FDD_Q_OffsetRange_r16__dB_5
 | UTRA_FDD_Q_OffsetRange_r16__dB_4
 | UTRA_FDD_Q_OffsetRange_r16__dB_3
 | UTRA_FDD_Q_OffsetRange_r16__dB_2
 | UTRA_FDD_Q_OffsetRange_r16__dB_1
 | UTRA_FDD_Q_OffsetRange_r16__dB0
 | UTRA_FDD_Q_OffsetRange_r16__dB1
 | UTRA_FDD_Q_OffsetRange_r16__dB2
 | UTRA_FDD_Q_OffsetRange_r16__dB3
 | UTRA_FDD_Q_OffsetRange_r16__dB4
 | UTRA_FDD_Q_OffsetRange_r16__dB5
 | UTRA_FDD_Q_OffsetRange_r16__dB6
 | UTRA_FDD_Q_OffsetRange_r16__dB8
 | UTRA_FDD_Q_OffsetRange_r16__dB10
 | UTRA_FDD_Q_OffsetRange_r16__dB12
 | UTRA_FDD_Q_OffsetRange_r16__dB14
 | UTRA_FDD_Q_OffsetRange_r16__dB16
 | UTRA_FDD_Q_OffsetRange_r16__dB18
 | UTRA_FDD_Q_OffsetRange_r16__dB20
 | UTRA_FDD_Q_OffsetRange_r16__dB22
 | UTRA_FDD_Q_OffsetRange_r16__dB24
.
Definition UTRA_FDD_Q_OffsetRange_r16__cond := (fun (_ : UTRA_FDD_Q_OffsetRange_r16__Type) => True).
Lemma UTRA_FDD_Q_OffsetRange_r16__nat__helper : to_bit_sz 30 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UTRA_FDD_Q_OffsetRange_r16__nat__Format : T_Format nat (fun z => (z <= 30)) :=
  nat_enum_format 30 UTRA_FDD_Q_OffsetRange_r16__nat__helper.

Definition UTRA_FDD_Q_OffsetRange_r16__F1 t :=
  match t with
  | UTRA_FDD_Q_OffsetRange_r16__dB_24 => 0
  | UTRA_FDD_Q_OffsetRange_r16__dB_22 => 1
  | UTRA_FDD_Q_OffsetRange_r16__dB_20 => 2
  | UTRA_FDD_Q_OffsetRange_r16__dB_18 => 3
  | UTRA_FDD_Q_OffsetRange_r16__dB_16 => 4
  | UTRA_FDD_Q_OffsetRange_r16__dB_14 => 5
  | UTRA_FDD_Q_OffsetRange_r16__dB_12 => 6
  | UTRA_FDD_Q_OffsetRange_r16__dB_10 => 7
  | UTRA_FDD_Q_OffsetRange_r16__dB_8 => 8
  | UTRA_FDD_Q_OffsetRange_r16__dB_6 => 9
  | UTRA_FDD_Q_OffsetRange_r16__dB_5 => 10
  | UTRA_FDD_Q_OffsetRange_r16__dB_4 => 11
  | UTRA_FDD_Q_OffsetRange_r16__dB_3 => 12
  | UTRA_FDD_Q_OffsetRange_r16__dB_2 => 13
  | UTRA_FDD_Q_OffsetRange_r16__dB_1 => 14
  | UTRA_FDD_Q_OffsetRange_r16__dB0 => 15
  | UTRA_FDD_Q_OffsetRange_r16__dB1 => 16
  | UTRA_FDD_Q_OffsetRange_r16__dB2 => 17
  | UTRA_FDD_Q_OffsetRange_r16__dB3 => 18
  | UTRA_FDD_Q_OffsetRange_r16__dB4 => 19
  | UTRA_FDD_Q_OffsetRange_r16__dB5 => 20
  | UTRA_FDD_Q_OffsetRange_r16__dB6 => 21
  | UTRA_FDD_Q_OffsetRange_r16__dB8 => 22
  | UTRA_FDD_Q_OffsetRange_r16__dB10 => 23
  | UTRA_FDD_Q_OffsetRange_r16__dB12 => 24
  | UTRA_FDD_Q_OffsetRange_r16__dB14 => 25
  | UTRA_FDD_Q_OffsetRange_r16__dB16 => 26
  | UTRA_FDD_Q_OffsetRange_r16__dB18 => 27
  | UTRA_FDD_Q_OffsetRange_r16__dB20 => 28
  | UTRA_FDD_Q_OffsetRange_r16__dB22 => 29
  | UTRA_FDD_Q_OffsetRange_r16__dB24 => 30
  end.
Definition UTRA_FDD_Q_OffsetRange_r16__F2 n :=
  match n with
  | 0 => UTRA_FDD_Q_OffsetRange_r16__dB_24
  | 1 => UTRA_FDD_Q_OffsetRange_r16__dB_22
  | 2 => UTRA_FDD_Q_OffsetRange_r16__dB_20
  | 3 => UTRA_FDD_Q_OffsetRange_r16__dB_18
  | 4 => UTRA_FDD_Q_OffsetRange_r16__dB_16
  | 5 => UTRA_FDD_Q_OffsetRange_r16__dB_14
  | 6 => UTRA_FDD_Q_OffsetRange_r16__dB_12
  | 7 => UTRA_FDD_Q_OffsetRange_r16__dB_10
  | 8 => UTRA_FDD_Q_OffsetRange_r16__dB_8
  | 9 => UTRA_FDD_Q_OffsetRange_r16__dB_6
  | 10 => UTRA_FDD_Q_OffsetRange_r16__dB_5
  | 11 => UTRA_FDD_Q_OffsetRange_r16__dB_4
  | 12 => UTRA_FDD_Q_OffsetRange_r16__dB_3
  | 13 => UTRA_FDD_Q_OffsetRange_r16__dB_2
  | 14 => UTRA_FDD_Q_OffsetRange_r16__dB_1
  | 15 => UTRA_FDD_Q_OffsetRange_r16__dB0
  | 16 => UTRA_FDD_Q_OffsetRange_r16__dB1
  | 17 => UTRA_FDD_Q_OffsetRange_r16__dB2
  | 18 => UTRA_FDD_Q_OffsetRange_r16__dB3
  | 19 => UTRA_FDD_Q_OffsetRange_r16__dB4
  | 20 => UTRA_FDD_Q_OffsetRange_r16__dB5
  | 21 => UTRA_FDD_Q_OffsetRange_r16__dB6
  | 22 => UTRA_FDD_Q_OffsetRange_r16__dB8
  | 23 => UTRA_FDD_Q_OffsetRange_r16__dB10
  | 24 => UTRA_FDD_Q_OffsetRange_r16__dB12
  | 25 => UTRA_FDD_Q_OffsetRange_r16__dB14
  | 26 => UTRA_FDD_Q_OffsetRange_r16__dB16
  | 27 => UTRA_FDD_Q_OffsetRange_r16__dB18
  | 28 => UTRA_FDD_Q_OffsetRange_r16__dB20
  | 29 => UTRA_FDD_Q_OffsetRange_r16__dB22
  | 30 => UTRA_FDD_Q_OffsetRange_r16__dB24
  | _ => UTRA_FDD_Q_OffsetRange_r16__dB_24
  end.
Lemma UTRA_FDD_Q_OffsetRange_r16__F1F2 : forall x : UTRA_FDD_Q_OffsetRange_r16__Type, (UTRA_FDD_Q_OffsetRange_r16__F1 x <= 30) /\ UTRA_FDD_Q_OffsetRange_r16__F2 (UTRA_FDD_Q_OffsetRange_r16__F1 x) = x. imp_solve. Qed.
Lemma UTRA_FDD_Q_OffsetRange_r16__F2F1 : forall (y : nat) (H : y <= 30), UTRA_FDD_Q_OffsetRange_r16__F1 (UTRA_FDD_Q_OffsetRange_r16__F2 y) = y. enum_solve H y. Qed.


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
Definition UTRA_FDD_Q_OffsetRange_r16__Format : T_Format UTRA_FDD_Q_OffsetRange_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UTRA_FDD_Q_OffsetRange_r16__nat__Format UTRA_FDD_Q_OffsetRange_r16__F1 UTRA_FDD_Q_OffsetRange_r16__F2 UTRA_FDD_Q_OffsetRange_r16__F1F2 UTRA_FDD_Q_OffsetRange_r16__F2F1.

Opaque UTRA_FDD_Q_OffsetRange_r16__cond UTRA_FDD_Q_OffsetRange_r16__Format.

