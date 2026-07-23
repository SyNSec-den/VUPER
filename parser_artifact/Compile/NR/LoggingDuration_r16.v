Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive LoggingDuration_r16__Type : Set :=
 | LoggingDuration_r16__min10
 | LoggingDuration_r16__min20
 | LoggingDuration_r16__min40
 | LoggingDuration_r16__min60
 | LoggingDuration_r16__min90
 | LoggingDuration_r16__min120
 | LoggingDuration_r16__spare2
 | LoggingDuration_r16__spare1
.
Definition LoggingDuration_r16__cond := (fun (_ : LoggingDuration_r16__Type) => True).
Lemma LoggingDuration_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LoggingDuration_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 LoggingDuration_r16__nat__helper.

Definition LoggingDuration_r16__F1 t :=
  match t with
  | LoggingDuration_r16__min10 => 0
  | LoggingDuration_r16__min20 => 1
  | LoggingDuration_r16__min40 => 2
  | LoggingDuration_r16__min60 => 3
  | LoggingDuration_r16__min90 => 4
  | LoggingDuration_r16__min120 => 5
  | LoggingDuration_r16__spare2 => 6
  | LoggingDuration_r16__spare1 => 7
  end.
Definition LoggingDuration_r16__F2 n :=
  match n with
  | 0 => LoggingDuration_r16__min10
  | 1 => LoggingDuration_r16__min20
  | 2 => LoggingDuration_r16__min40
  | 3 => LoggingDuration_r16__min60
  | 4 => LoggingDuration_r16__min90
  | 5 => LoggingDuration_r16__min120
  | 6 => LoggingDuration_r16__spare2
  | 7 => LoggingDuration_r16__spare1
  | _ => LoggingDuration_r16__min10
  end.
Lemma LoggingDuration_r16__F1F2 : forall x : LoggingDuration_r16__Type, (LoggingDuration_r16__F1 x <= 7) /\ LoggingDuration_r16__F2 (LoggingDuration_r16__F1 x) = x. imp_solve. Qed.
Lemma LoggingDuration_r16__F2F1 : forall (y : nat) (H : y <= 7), LoggingDuration_r16__F1 (LoggingDuration_r16__F2 y) = y. enum_solve H y. Qed.


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
Definition LoggingDuration_r16__Format : T_Format LoggingDuration_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LoggingDuration_r16__nat__Format LoggingDuration_r16__F1 LoggingDuration_r16__F2 LoggingDuration_r16__F1F2 LoggingDuration_r16__F2F1.

Opaque LoggingDuration_r16__cond LoggingDuration_r16__Format.

