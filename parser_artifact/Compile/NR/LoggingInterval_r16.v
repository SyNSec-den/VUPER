Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive LoggingInterval_r16__Type : Set :=
 | LoggingInterval_r16__ms320
 | LoggingInterval_r16__ms640
 | LoggingInterval_r16__ms1280
 | LoggingInterval_r16__ms2560
 | LoggingInterval_r16__ms5120
 | LoggingInterval_r16__ms10240
 | LoggingInterval_r16__ms20480
 | LoggingInterval_r16__ms30720
 | LoggingInterval_r16__ms40960
 | LoggingInterval_r16__ms61440
 | LoggingInterval_r16__infinity
.
Definition LoggingInterval_r16__cond := (fun (_ : LoggingInterval_r16__Type) => True).
Lemma LoggingInterval_r16__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LoggingInterval_r16__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 LoggingInterval_r16__nat__helper.

Definition LoggingInterval_r16__F1 t :=
  match t with
  | LoggingInterval_r16__ms320 => 0
  | LoggingInterval_r16__ms640 => 1
  | LoggingInterval_r16__ms1280 => 2
  | LoggingInterval_r16__ms2560 => 3
  | LoggingInterval_r16__ms5120 => 4
  | LoggingInterval_r16__ms10240 => 5
  | LoggingInterval_r16__ms20480 => 6
  | LoggingInterval_r16__ms30720 => 7
  | LoggingInterval_r16__ms40960 => 8
  | LoggingInterval_r16__ms61440 => 9
  | LoggingInterval_r16__infinity => 10
  end.
Definition LoggingInterval_r16__F2 n :=
  match n with
  | 0 => LoggingInterval_r16__ms320
  | 1 => LoggingInterval_r16__ms640
  | 2 => LoggingInterval_r16__ms1280
  | 3 => LoggingInterval_r16__ms2560
  | 4 => LoggingInterval_r16__ms5120
  | 5 => LoggingInterval_r16__ms10240
  | 6 => LoggingInterval_r16__ms20480
  | 7 => LoggingInterval_r16__ms30720
  | 8 => LoggingInterval_r16__ms40960
  | 9 => LoggingInterval_r16__ms61440
  | 10 => LoggingInterval_r16__infinity
  | _ => LoggingInterval_r16__ms320
  end.
Lemma LoggingInterval_r16__F1F2 : forall x : LoggingInterval_r16__Type, (LoggingInterval_r16__F1 x <= 10) /\ LoggingInterval_r16__F2 (LoggingInterval_r16__F1 x) = x. imp_solve. Qed.
Lemma LoggingInterval_r16__F2F1 : forall (y : nat) (H : y <= 10), LoggingInterval_r16__F1 (LoggingInterval_r16__F2 y) = y. enum_solve H y. Qed.


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
Definition LoggingInterval_r16__Format : T_Format LoggingInterval_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LoggingInterval_r16__nat__Format LoggingInterval_r16__F1 LoggingInterval_r16__F2 LoggingInterval_r16__F1F2 LoggingInterval_r16__F2F1.

Opaque LoggingInterval_r16__cond LoggingInterval_r16__Format.

