Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SL_TimeOffsetEUTRA_r16__Type : Set :=
 | SL_TimeOffsetEUTRA_r16__ms0
 | SL_TimeOffsetEUTRA_r16__ms0dot25
 | SL_TimeOffsetEUTRA_r16__ms0dot5
 | SL_TimeOffsetEUTRA_r16__ms0dot625
 | SL_TimeOffsetEUTRA_r16__ms0dot75
 | SL_TimeOffsetEUTRA_r16__ms1
 | SL_TimeOffsetEUTRA_r16__ms1dot25
 | SL_TimeOffsetEUTRA_r16__ms1dot5
 | SL_TimeOffsetEUTRA_r16__ms1dot75
 | SL_TimeOffsetEUTRA_r16__ms2
 | SL_TimeOffsetEUTRA_r16__ms2dot5
 | SL_TimeOffsetEUTRA_r16__ms3
 | SL_TimeOffsetEUTRA_r16__ms4
 | SL_TimeOffsetEUTRA_r16__ms5
 | SL_TimeOffsetEUTRA_r16__ms6
 | SL_TimeOffsetEUTRA_r16__ms8
 | SL_TimeOffsetEUTRA_r16__ms10
 | SL_TimeOffsetEUTRA_r16__ms20
.
Definition SL_TimeOffsetEUTRA_r16__cond := (fun (_ : SL_TimeOffsetEUTRA_r16__Type) => True).
Lemma SL_TimeOffsetEUTRA_r16__nat__helper : to_bit_sz 17 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_TimeOffsetEUTRA_r16__nat__Format : T_Format nat (fun z => (z <= 17)) :=
  nat_enum_format 17 SL_TimeOffsetEUTRA_r16__nat__helper.

Definition SL_TimeOffsetEUTRA_r16__F1 t :=
  match t with
  | SL_TimeOffsetEUTRA_r16__ms0 => 0
  | SL_TimeOffsetEUTRA_r16__ms0dot25 => 1
  | SL_TimeOffsetEUTRA_r16__ms0dot5 => 2
  | SL_TimeOffsetEUTRA_r16__ms0dot625 => 3
  | SL_TimeOffsetEUTRA_r16__ms0dot75 => 4
  | SL_TimeOffsetEUTRA_r16__ms1 => 5
  | SL_TimeOffsetEUTRA_r16__ms1dot25 => 6
  | SL_TimeOffsetEUTRA_r16__ms1dot5 => 7
  | SL_TimeOffsetEUTRA_r16__ms1dot75 => 8
  | SL_TimeOffsetEUTRA_r16__ms2 => 9
  | SL_TimeOffsetEUTRA_r16__ms2dot5 => 10
  | SL_TimeOffsetEUTRA_r16__ms3 => 11
  | SL_TimeOffsetEUTRA_r16__ms4 => 12
  | SL_TimeOffsetEUTRA_r16__ms5 => 13
  | SL_TimeOffsetEUTRA_r16__ms6 => 14
  | SL_TimeOffsetEUTRA_r16__ms8 => 15
  | SL_TimeOffsetEUTRA_r16__ms10 => 16
  | SL_TimeOffsetEUTRA_r16__ms20 => 17
  end.
Definition SL_TimeOffsetEUTRA_r16__F2 n :=
  match n with
  | 0 => SL_TimeOffsetEUTRA_r16__ms0
  | 1 => SL_TimeOffsetEUTRA_r16__ms0dot25
  | 2 => SL_TimeOffsetEUTRA_r16__ms0dot5
  | 3 => SL_TimeOffsetEUTRA_r16__ms0dot625
  | 4 => SL_TimeOffsetEUTRA_r16__ms0dot75
  | 5 => SL_TimeOffsetEUTRA_r16__ms1
  | 6 => SL_TimeOffsetEUTRA_r16__ms1dot25
  | 7 => SL_TimeOffsetEUTRA_r16__ms1dot5
  | 8 => SL_TimeOffsetEUTRA_r16__ms1dot75
  | 9 => SL_TimeOffsetEUTRA_r16__ms2
  | 10 => SL_TimeOffsetEUTRA_r16__ms2dot5
  | 11 => SL_TimeOffsetEUTRA_r16__ms3
  | 12 => SL_TimeOffsetEUTRA_r16__ms4
  | 13 => SL_TimeOffsetEUTRA_r16__ms5
  | 14 => SL_TimeOffsetEUTRA_r16__ms6
  | 15 => SL_TimeOffsetEUTRA_r16__ms8
  | 16 => SL_TimeOffsetEUTRA_r16__ms10
  | 17 => SL_TimeOffsetEUTRA_r16__ms20
  | _ => SL_TimeOffsetEUTRA_r16__ms0
  end.
Lemma SL_TimeOffsetEUTRA_r16__F1F2 : forall x : SL_TimeOffsetEUTRA_r16__Type, (SL_TimeOffsetEUTRA_r16__F1 x <= 17) /\ SL_TimeOffsetEUTRA_r16__F2 (SL_TimeOffsetEUTRA_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_TimeOffsetEUTRA_r16__F2F1 : forall (y : nat) (H : y <= 17), SL_TimeOffsetEUTRA_r16__F1 (SL_TimeOffsetEUTRA_r16__F2 y) = y. enum_solve H y. Qed.


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
Definition SL_TimeOffsetEUTRA_r16__Format : T_Format SL_TimeOffsetEUTRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_TimeOffsetEUTRA_r16__nat__Format SL_TimeOffsetEUTRA_r16__F1 SL_TimeOffsetEUTRA_r16__F2 SL_TimeOffsetEUTRA_r16__F1F2 SL_TimeOffsetEUTRA_r16__F2F1.

Opaque SL_TimeOffsetEUTRA_r16__cond SL_TimeOffsetEUTRA_r16__Format.

