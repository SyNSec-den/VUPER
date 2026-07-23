Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive T_Reassembly__Type : Set :=
 | T_Reassembly__ms0
 | T_Reassembly__ms5
 | T_Reassembly__ms10
 | T_Reassembly__ms15
 | T_Reassembly__ms20
 | T_Reassembly__ms25
 | T_Reassembly__ms30
 | T_Reassembly__ms35
 | T_Reassembly__ms40
 | T_Reassembly__ms45
 | T_Reassembly__ms50
 | T_Reassembly__ms55
 | T_Reassembly__ms60
 | T_Reassembly__ms65
 | T_Reassembly__ms70
 | T_Reassembly__ms75
 | T_Reassembly__ms80
 | T_Reassembly__ms85
 | T_Reassembly__ms90
 | T_Reassembly__ms95
 | T_Reassembly__ms100
 | T_Reassembly__ms110
 | T_Reassembly__ms120
 | T_Reassembly__ms130
 | T_Reassembly__ms140
 | T_Reassembly__ms150
 | T_Reassembly__ms160
 | T_Reassembly__ms170
 | T_Reassembly__ms180
 | T_Reassembly__ms190
 | T_Reassembly__ms200
 | T_Reassembly__spare1
.
Definition T_Reassembly__cond := (fun (_ : T_Reassembly__Type) => True).
Lemma T_Reassembly__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition T_Reassembly__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 T_Reassembly__nat__helper.

Definition T_Reassembly__F1 t :=
  match t with
  | T_Reassembly__ms0 => 0
  | T_Reassembly__ms5 => 1
  | T_Reassembly__ms10 => 2
  | T_Reassembly__ms15 => 3
  | T_Reassembly__ms20 => 4
  | T_Reassembly__ms25 => 5
  | T_Reassembly__ms30 => 6
  | T_Reassembly__ms35 => 7
  | T_Reassembly__ms40 => 8
  | T_Reassembly__ms45 => 9
  | T_Reassembly__ms50 => 10
  | T_Reassembly__ms55 => 11
  | T_Reassembly__ms60 => 12
  | T_Reassembly__ms65 => 13
  | T_Reassembly__ms70 => 14
  | T_Reassembly__ms75 => 15
  | T_Reassembly__ms80 => 16
  | T_Reassembly__ms85 => 17
  | T_Reassembly__ms90 => 18
  | T_Reassembly__ms95 => 19
  | T_Reassembly__ms100 => 20
  | T_Reassembly__ms110 => 21
  | T_Reassembly__ms120 => 22
  | T_Reassembly__ms130 => 23
  | T_Reassembly__ms140 => 24
  | T_Reassembly__ms150 => 25
  | T_Reassembly__ms160 => 26
  | T_Reassembly__ms170 => 27
  | T_Reassembly__ms180 => 28
  | T_Reassembly__ms190 => 29
  | T_Reassembly__ms200 => 30
  | T_Reassembly__spare1 => 31
  end.
Definition T_Reassembly__F2 n :=
  match n with
  | 0 => T_Reassembly__ms0
  | 1 => T_Reassembly__ms5
  | 2 => T_Reassembly__ms10
  | 3 => T_Reassembly__ms15
  | 4 => T_Reassembly__ms20
  | 5 => T_Reassembly__ms25
  | 6 => T_Reassembly__ms30
  | 7 => T_Reassembly__ms35
  | 8 => T_Reassembly__ms40
  | 9 => T_Reassembly__ms45
  | 10 => T_Reassembly__ms50
  | 11 => T_Reassembly__ms55
  | 12 => T_Reassembly__ms60
  | 13 => T_Reassembly__ms65
  | 14 => T_Reassembly__ms70
  | 15 => T_Reassembly__ms75
  | 16 => T_Reassembly__ms80
  | 17 => T_Reassembly__ms85
  | 18 => T_Reassembly__ms90
  | 19 => T_Reassembly__ms95
  | 20 => T_Reassembly__ms100
  | 21 => T_Reassembly__ms110
  | 22 => T_Reassembly__ms120
  | 23 => T_Reassembly__ms130
  | 24 => T_Reassembly__ms140
  | 25 => T_Reassembly__ms150
  | 26 => T_Reassembly__ms160
  | 27 => T_Reassembly__ms170
  | 28 => T_Reassembly__ms180
  | 29 => T_Reassembly__ms190
  | 30 => T_Reassembly__ms200
  | 31 => T_Reassembly__spare1
  | _ => T_Reassembly__ms0
  end.
Lemma T_Reassembly__F1F2 : forall x : T_Reassembly__Type, (T_Reassembly__F1 x <= 31) /\ T_Reassembly__F2 (T_Reassembly__F1 x) = x. imp_solve. Qed.
Lemma T_Reassembly__F2F1 : forall (y : nat) (H : y <= 31), T_Reassembly__F1 (T_Reassembly__F2 y) = y. enum_solve H y. Qed.


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
Definition T_Reassembly__Format : T_Format T_Reassembly__Type (fun _ => True) :=
(* Eval compute in *) proj3_format T_Reassembly__nat__Format T_Reassembly__F1 T_Reassembly__F2 T_Reassembly__F1F2 T_Reassembly__F2F1.

Opaque T_Reassembly__cond T_Reassembly__Format.

