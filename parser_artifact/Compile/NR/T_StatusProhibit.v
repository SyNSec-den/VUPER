Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive T_StatusProhibit__Type : Set :=
 | T_StatusProhibit__ms0
 | T_StatusProhibit__ms5
 | T_StatusProhibit__ms10
 | T_StatusProhibit__ms15
 | T_StatusProhibit__ms20
 | T_StatusProhibit__ms25
 | T_StatusProhibit__ms30
 | T_StatusProhibit__ms35
 | T_StatusProhibit__ms40
 | T_StatusProhibit__ms45
 | T_StatusProhibit__ms50
 | T_StatusProhibit__ms55
 | T_StatusProhibit__ms60
 | T_StatusProhibit__ms65
 | T_StatusProhibit__ms70
 | T_StatusProhibit__ms75
 | T_StatusProhibit__ms80
 | T_StatusProhibit__ms85
 | T_StatusProhibit__ms90
 | T_StatusProhibit__ms95
 | T_StatusProhibit__ms100
 | T_StatusProhibit__ms105
 | T_StatusProhibit__ms110
 | T_StatusProhibit__ms115
 | T_StatusProhibit__ms120
 | T_StatusProhibit__ms125
 | T_StatusProhibit__ms130
 | T_StatusProhibit__ms135
 | T_StatusProhibit__ms140
 | T_StatusProhibit__ms145
 | T_StatusProhibit__ms150
 | T_StatusProhibit__ms155
 | T_StatusProhibit__ms160
 | T_StatusProhibit__ms165
 | T_StatusProhibit__ms170
 | T_StatusProhibit__ms175
 | T_StatusProhibit__ms180
 | T_StatusProhibit__ms185
 | T_StatusProhibit__ms190
 | T_StatusProhibit__ms195
 | T_StatusProhibit__ms200
 | T_StatusProhibit__ms205
 | T_StatusProhibit__ms210
 | T_StatusProhibit__ms215
 | T_StatusProhibit__ms220
 | T_StatusProhibit__ms225
 | T_StatusProhibit__ms230
 | T_StatusProhibit__ms235
 | T_StatusProhibit__ms240
 | T_StatusProhibit__ms245
 | T_StatusProhibit__ms250
 | T_StatusProhibit__ms300
 | T_StatusProhibit__ms350
 | T_StatusProhibit__ms400
 | T_StatusProhibit__ms450
 | T_StatusProhibit__ms500
 | T_StatusProhibit__ms800
 | T_StatusProhibit__ms1000
 | T_StatusProhibit__ms1200
 | T_StatusProhibit__ms1600
 | T_StatusProhibit__ms2000
 | T_StatusProhibit__ms2400
 | T_StatusProhibit__spare2
 | T_StatusProhibit__spare1
.
Definition T_StatusProhibit__cond := (fun (_ : T_StatusProhibit__Type) => True).
Lemma T_StatusProhibit__nat__helper : to_bit_sz 63 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition T_StatusProhibit__nat__Format : T_Format nat (fun z => (z <= 63)) :=
  nat_enum_format 63 T_StatusProhibit__nat__helper.

Definition T_StatusProhibit__F1 t :=
  match t with
  | T_StatusProhibit__ms0 => 0
  | T_StatusProhibit__ms5 => 1
  | T_StatusProhibit__ms10 => 2
  | T_StatusProhibit__ms15 => 3
  | T_StatusProhibit__ms20 => 4
  | T_StatusProhibit__ms25 => 5
  | T_StatusProhibit__ms30 => 6
  | T_StatusProhibit__ms35 => 7
  | T_StatusProhibit__ms40 => 8
  | T_StatusProhibit__ms45 => 9
  | T_StatusProhibit__ms50 => 10
  | T_StatusProhibit__ms55 => 11
  | T_StatusProhibit__ms60 => 12
  | T_StatusProhibit__ms65 => 13
  | T_StatusProhibit__ms70 => 14
  | T_StatusProhibit__ms75 => 15
  | T_StatusProhibit__ms80 => 16
  | T_StatusProhibit__ms85 => 17
  | T_StatusProhibit__ms90 => 18
  | T_StatusProhibit__ms95 => 19
  | T_StatusProhibit__ms100 => 20
  | T_StatusProhibit__ms105 => 21
  | T_StatusProhibit__ms110 => 22
  | T_StatusProhibit__ms115 => 23
  | T_StatusProhibit__ms120 => 24
  | T_StatusProhibit__ms125 => 25
  | T_StatusProhibit__ms130 => 26
  | T_StatusProhibit__ms135 => 27
  | T_StatusProhibit__ms140 => 28
  | T_StatusProhibit__ms145 => 29
  | T_StatusProhibit__ms150 => 30
  | T_StatusProhibit__ms155 => 31
  | T_StatusProhibit__ms160 => 32
  | T_StatusProhibit__ms165 => 33
  | T_StatusProhibit__ms170 => 34
  | T_StatusProhibit__ms175 => 35
  | T_StatusProhibit__ms180 => 36
  | T_StatusProhibit__ms185 => 37
  | T_StatusProhibit__ms190 => 38
  | T_StatusProhibit__ms195 => 39
  | T_StatusProhibit__ms200 => 40
  | T_StatusProhibit__ms205 => 41
  | T_StatusProhibit__ms210 => 42
  | T_StatusProhibit__ms215 => 43
  | T_StatusProhibit__ms220 => 44
  | T_StatusProhibit__ms225 => 45
  | T_StatusProhibit__ms230 => 46
  | T_StatusProhibit__ms235 => 47
  | T_StatusProhibit__ms240 => 48
  | T_StatusProhibit__ms245 => 49
  | T_StatusProhibit__ms250 => 50
  | T_StatusProhibit__ms300 => 51
  | T_StatusProhibit__ms350 => 52
  | T_StatusProhibit__ms400 => 53
  | T_StatusProhibit__ms450 => 54
  | T_StatusProhibit__ms500 => 55
  | T_StatusProhibit__ms800 => 56
  | T_StatusProhibit__ms1000 => 57
  | T_StatusProhibit__ms1200 => 58
  | T_StatusProhibit__ms1600 => 59
  | T_StatusProhibit__ms2000 => 60
  | T_StatusProhibit__ms2400 => 61
  | T_StatusProhibit__spare2 => 62
  | T_StatusProhibit__spare1 => 63
  end.
Definition T_StatusProhibit__F2 n :=
  match n with
  | 0 => T_StatusProhibit__ms0
  | 1 => T_StatusProhibit__ms5
  | 2 => T_StatusProhibit__ms10
  | 3 => T_StatusProhibit__ms15
  | 4 => T_StatusProhibit__ms20
  | 5 => T_StatusProhibit__ms25
  | 6 => T_StatusProhibit__ms30
  | 7 => T_StatusProhibit__ms35
  | 8 => T_StatusProhibit__ms40
  | 9 => T_StatusProhibit__ms45
  | 10 => T_StatusProhibit__ms50
  | 11 => T_StatusProhibit__ms55
  | 12 => T_StatusProhibit__ms60
  | 13 => T_StatusProhibit__ms65
  | 14 => T_StatusProhibit__ms70
  | 15 => T_StatusProhibit__ms75
  | 16 => T_StatusProhibit__ms80
  | 17 => T_StatusProhibit__ms85
  | 18 => T_StatusProhibit__ms90
  | 19 => T_StatusProhibit__ms95
  | 20 => T_StatusProhibit__ms100
  | 21 => T_StatusProhibit__ms105
  | 22 => T_StatusProhibit__ms110
  | 23 => T_StatusProhibit__ms115
  | 24 => T_StatusProhibit__ms120
  | 25 => T_StatusProhibit__ms125
  | 26 => T_StatusProhibit__ms130
  | 27 => T_StatusProhibit__ms135
  | 28 => T_StatusProhibit__ms140
  | 29 => T_StatusProhibit__ms145
  | 30 => T_StatusProhibit__ms150
  | 31 => T_StatusProhibit__ms155
  | 32 => T_StatusProhibit__ms160
  | 33 => T_StatusProhibit__ms165
  | 34 => T_StatusProhibit__ms170
  | 35 => T_StatusProhibit__ms175
  | 36 => T_StatusProhibit__ms180
  | 37 => T_StatusProhibit__ms185
  | 38 => T_StatusProhibit__ms190
  | 39 => T_StatusProhibit__ms195
  | 40 => T_StatusProhibit__ms200
  | 41 => T_StatusProhibit__ms205
  | 42 => T_StatusProhibit__ms210
  | 43 => T_StatusProhibit__ms215
  | 44 => T_StatusProhibit__ms220
  | 45 => T_StatusProhibit__ms225
  | 46 => T_StatusProhibit__ms230
  | 47 => T_StatusProhibit__ms235
  | 48 => T_StatusProhibit__ms240
  | 49 => T_StatusProhibit__ms245
  | 50 => T_StatusProhibit__ms250
  | 51 => T_StatusProhibit__ms300
  | 52 => T_StatusProhibit__ms350
  | 53 => T_StatusProhibit__ms400
  | 54 => T_StatusProhibit__ms450
  | 55 => T_StatusProhibit__ms500
  | 56 => T_StatusProhibit__ms800
  | 57 => T_StatusProhibit__ms1000
  | 58 => T_StatusProhibit__ms1200
  | 59 => T_StatusProhibit__ms1600
  | 60 => T_StatusProhibit__ms2000
  | 61 => T_StatusProhibit__ms2400
  | 62 => T_StatusProhibit__spare2
  | 63 => T_StatusProhibit__spare1
  | _ => T_StatusProhibit__ms0
  end.
Lemma T_StatusProhibit__F1F2 : forall x : T_StatusProhibit__Type, (T_StatusProhibit__F1 x <= 63) /\ T_StatusProhibit__F2 (T_StatusProhibit__F1 x) = x. imp_solve. Qed.
Lemma T_StatusProhibit__F2F1 : forall (y : nat) (H : y <= 63), T_StatusProhibit__F1 (T_StatusProhibit__F2 y) = y. enum_solve H y. Qed.


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
Definition T_StatusProhibit__Format : T_Format T_StatusProhibit__Type (fun _ => True) :=
(* Eval compute in *) proj3_format T_StatusProhibit__nat__Format T_StatusProhibit__F1 T_StatusProhibit__F2 T_StatusProhibit__F1F2 T_StatusProhibit__F2F1.

Opaque T_StatusProhibit__cond T_StatusProhibit__Format.

