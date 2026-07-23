Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive T_PollRetransmit__Type : Set :=
 | T_PollRetransmit__ms5
 | T_PollRetransmit__ms10
 | T_PollRetransmit__ms15
 | T_PollRetransmit__ms20
 | T_PollRetransmit__ms25
 | T_PollRetransmit__ms30
 | T_PollRetransmit__ms35
 | T_PollRetransmit__ms40
 | T_PollRetransmit__ms45
 | T_PollRetransmit__ms50
 | T_PollRetransmit__ms55
 | T_PollRetransmit__ms60
 | T_PollRetransmit__ms65
 | T_PollRetransmit__ms70
 | T_PollRetransmit__ms75
 | T_PollRetransmit__ms80
 | T_PollRetransmit__ms85
 | T_PollRetransmit__ms90
 | T_PollRetransmit__ms95
 | T_PollRetransmit__ms100
 | T_PollRetransmit__ms105
 | T_PollRetransmit__ms110
 | T_PollRetransmit__ms115
 | T_PollRetransmit__ms120
 | T_PollRetransmit__ms125
 | T_PollRetransmit__ms130
 | T_PollRetransmit__ms135
 | T_PollRetransmit__ms140
 | T_PollRetransmit__ms145
 | T_PollRetransmit__ms150
 | T_PollRetransmit__ms155
 | T_PollRetransmit__ms160
 | T_PollRetransmit__ms165
 | T_PollRetransmit__ms170
 | T_PollRetransmit__ms175
 | T_PollRetransmit__ms180
 | T_PollRetransmit__ms185
 | T_PollRetransmit__ms190
 | T_PollRetransmit__ms195
 | T_PollRetransmit__ms200
 | T_PollRetransmit__ms205
 | T_PollRetransmit__ms210
 | T_PollRetransmit__ms215
 | T_PollRetransmit__ms220
 | T_PollRetransmit__ms225
 | T_PollRetransmit__ms230
 | T_PollRetransmit__ms235
 | T_PollRetransmit__ms240
 | T_PollRetransmit__ms245
 | T_PollRetransmit__ms250
 | T_PollRetransmit__ms300
 | T_PollRetransmit__ms350
 | T_PollRetransmit__ms400
 | T_PollRetransmit__ms450
 | T_PollRetransmit__ms500
 | T_PollRetransmit__ms800
 | T_PollRetransmit__ms1000
 | T_PollRetransmit__ms2000
 | T_PollRetransmit__ms4000
 | T_PollRetransmit__ms1_v1610
 | T_PollRetransmit__ms2_v1610
 | T_PollRetransmit__ms3_v1610
 | T_PollRetransmit__ms4_v1610
 | T_PollRetransmit__spare1
.
Definition T_PollRetransmit__cond := (fun (_ : T_PollRetransmit__Type) => True).
Lemma T_PollRetransmit__nat__helper : to_bit_sz 63 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition T_PollRetransmit__nat__Format : T_Format nat (fun z => (z <= 63)) :=
  nat_enum_format 63 T_PollRetransmit__nat__helper.

Definition T_PollRetransmit__F1 t :=
  match t with
  | T_PollRetransmit__ms5 => 0
  | T_PollRetransmit__ms10 => 1
  | T_PollRetransmit__ms15 => 2
  | T_PollRetransmit__ms20 => 3
  | T_PollRetransmit__ms25 => 4
  | T_PollRetransmit__ms30 => 5
  | T_PollRetransmit__ms35 => 6
  | T_PollRetransmit__ms40 => 7
  | T_PollRetransmit__ms45 => 8
  | T_PollRetransmit__ms50 => 9
  | T_PollRetransmit__ms55 => 10
  | T_PollRetransmit__ms60 => 11
  | T_PollRetransmit__ms65 => 12
  | T_PollRetransmit__ms70 => 13
  | T_PollRetransmit__ms75 => 14
  | T_PollRetransmit__ms80 => 15
  | T_PollRetransmit__ms85 => 16
  | T_PollRetransmit__ms90 => 17
  | T_PollRetransmit__ms95 => 18
  | T_PollRetransmit__ms100 => 19
  | T_PollRetransmit__ms105 => 20
  | T_PollRetransmit__ms110 => 21
  | T_PollRetransmit__ms115 => 22
  | T_PollRetransmit__ms120 => 23
  | T_PollRetransmit__ms125 => 24
  | T_PollRetransmit__ms130 => 25
  | T_PollRetransmit__ms135 => 26
  | T_PollRetransmit__ms140 => 27
  | T_PollRetransmit__ms145 => 28
  | T_PollRetransmit__ms150 => 29
  | T_PollRetransmit__ms155 => 30
  | T_PollRetransmit__ms160 => 31
  | T_PollRetransmit__ms165 => 32
  | T_PollRetransmit__ms170 => 33
  | T_PollRetransmit__ms175 => 34
  | T_PollRetransmit__ms180 => 35
  | T_PollRetransmit__ms185 => 36
  | T_PollRetransmit__ms190 => 37
  | T_PollRetransmit__ms195 => 38
  | T_PollRetransmit__ms200 => 39
  | T_PollRetransmit__ms205 => 40
  | T_PollRetransmit__ms210 => 41
  | T_PollRetransmit__ms215 => 42
  | T_PollRetransmit__ms220 => 43
  | T_PollRetransmit__ms225 => 44
  | T_PollRetransmit__ms230 => 45
  | T_PollRetransmit__ms235 => 46
  | T_PollRetransmit__ms240 => 47
  | T_PollRetransmit__ms245 => 48
  | T_PollRetransmit__ms250 => 49
  | T_PollRetransmit__ms300 => 50
  | T_PollRetransmit__ms350 => 51
  | T_PollRetransmit__ms400 => 52
  | T_PollRetransmit__ms450 => 53
  | T_PollRetransmit__ms500 => 54
  | T_PollRetransmit__ms800 => 55
  | T_PollRetransmit__ms1000 => 56
  | T_PollRetransmit__ms2000 => 57
  | T_PollRetransmit__ms4000 => 58
  | T_PollRetransmit__ms1_v1610 => 59
  | T_PollRetransmit__ms2_v1610 => 60
  | T_PollRetransmit__ms3_v1610 => 61
  | T_PollRetransmit__ms4_v1610 => 62
  | T_PollRetransmit__spare1 => 63
  end.
Definition T_PollRetransmit__F2 n :=
  match n with
  | 0 => T_PollRetransmit__ms5
  | 1 => T_PollRetransmit__ms10
  | 2 => T_PollRetransmit__ms15
  | 3 => T_PollRetransmit__ms20
  | 4 => T_PollRetransmit__ms25
  | 5 => T_PollRetransmit__ms30
  | 6 => T_PollRetransmit__ms35
  | 7 => T_PollRetransmit__ms40
  | 8 => T_PollRetransmit__ms45
  | 9 => T_PollRetransmit__ms50
  | 10 => T_PollRetransmit__ms55
  | 11 => T_PollRetransmit__ms60
  | 12 => T_PollRetransmit__ms65
  | 13 => T_PollRetransmit__ms70
  | 14 => T_PollRetransmit__ms75
  | 15 => T_PollRetransmit__ms80
  | 16 => T_PollRetransmit__ms85
  | 17 => T_PollRetransmit__ms90
  | 18 => T_PollRetransmit__ms95
  | 19 => T_PollRetransmit__ms100
  | 20 => T_PollRetransmit__ms105
  | 21 => T_PollRetransmit__ms110
  | 22 => T_PollRetransmit__ms115
  | 23 => T_PollRetransmit__ms120
  | 24 => T_PollRetransmit__ms125
  | 25 => T_PollRetransmit__ms130
  | 26 => T_PollRetransmit__ms135
  | 27 => T_PollRetransmit__ms140
  | 28 => T_PollRetransmit__ms145
  | 29 => T_PollRetransmit__ms150
  | 30 => T_PollRetransmit__ms155
  | 31 => T_PollRetransmit__ms160
  | 32 => T_PollRetransmit__ms165
  | 33 => T_PollRetransmit__ms170
  | 34 => T_PollRetransmit__ms175
  | 35 => T_PollRetransmit__ms180
  | 36 => T_PollRetransmit__ms185
  | 37 => T_PollRetransmit__ms190
  | 38 => T_PollRetransmit__ms195
  | 39 => T_PollRetransmit__ms200
  | 40 => T_PollRetransmit__ms205
  | 41 => T_PollRetransmit__ms210
  | 42 => T_PollRetransmit__ms215
  | 43 => T_PollRetransmit__ms220
  | 44 => T_PollRetransmit__ms225
  | 45 => T_PollRetransmit__ms230
  | 46 => T_PollRetransmit__ms235
  | 47 => T_PollRetransmit__ms240
  | 48 => T_PollRetransmit__ms245
  | 49 => T_PollRetransmit__ms250
  | 50 => T_PollRetransmit__ms300
  | 51 => T_PollRetransmit__ms350
  | 52 => T_PollRetransmit__ms400
  | 53 => T_PollRetransmit__ms450
  | 54 => T_PollRetransmit__ms500
  | 55 => T_PollRetransmit__ms800
  | 56 => T_PollRetransmit__ms1000
  | 57 => T_PollRetransmit__ms2000
  | 58 => T_PollRetransmit__ms4000
  | 59 => T_PollRetransmit__ms1_v1610
  | 60 => T_PollRetransmit__ms2_v1610
  | 61 => T_PollRetransmit__ms3_v1610
  | 62 => T_PollRetransmit__ms4_v1610
  | 63 => T_PollRetransmit__spare1
  | _ => T_PollRetransmit__ms5
  end.
Lemma T_PollRetransmit__F1F2 : forall x : T_PollRetransmit__Type, (T_PollRetransmit__F1 x <= 63) /\ T_PollRetransmit__F2 (T_PollRetransmit__F1 x) = x. imp_solve. Qed.
Lemma T_PollRetransmit__F2F1 : forall (y : nat) (H : y <= 63), T_PollRetransmit__F1 (T_PollRetransmit__F2 y) = y. enum_solve H y. Qed.


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
Definition T_PollRetransmit__Format : T_Format T_PollRetransmit__Type (fun _ => True) :=
(* Eval compute in *) proj3_format T_PollRetransmit__nat__Format T_PollRetransmit__F1 T_PollRetransmit__F2 T_PollRetransmit__F1F2 T_PollRetransmit__F2F1.

Opaque T_PollRetransmit__cond T_PollRetransmit__Format.

