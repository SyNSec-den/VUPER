Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive TimeToTrigger__Type : Set :=
 | TimeToTrigger__ms0
 | TimeToTrigger__ms40
 | TimeToTrigger__ms64
 | TimeToTrigger__ms80
 | TimeToTrigger__ms100
 | TimeToTrigger__ms128
 | TimeToTrigger__ms160
 | TimeToTrigger__ms256
 | TimeToTrigger__ms320
 | TimeToTrigger__ms480
 | TimeToTrigger__ms512
 | TimeToTrigger__ms640
 | TimeToTrigger__ms1024
 | TimeToTrigger__ms1280
 | TimeToTrigger__ms2560
 | TimeToTrigger__ms5120
.
Definition TimeToTrigger__cond := (fun (_ : TimeToTrigger__Type) => True).
Lemma TimeToTrigger__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition TimeToTrigger__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 TimeToTrigger__nat__helper.

Definition TimeToTrigger__F1 t :=
  match t with
  | TimeToTrigger__ms0 => 0
  | TimeToTrigger__ms40 => 1
  | TimeToTrigger__ms64 => 2
  | TimeToTrigger__ms80 => 3
  | TimeToTrigger__ms100 => 4
  | TimeToTrigger__ms128 => 5
  | TimeToTrigger__ms160 => 6
  | TimeToTrigger__ms256 => 7
  | TimeToTrigger__ms320 => 8
  | TimeToTrigger__ms480 => 9
  | TimeToTrigger__ms512 => 10
  | TimeToTrigger__ms640 => 11
  | TimeToTrigger__ms1024 => 12
  | TimeToTrigger__ms1280 => 13
  | TimeToTrigger__ms2560 => 14
  | TimeToTrigger__ms5120 => 15
  end.
Definition TimeToTrigger__F2 n :=
  match n with
  | 0 => TimeToTrigger__ms0
  | 1 => TimeToTrigger__ms40
  | 2 => TimeToTrigger__ms64
  | 3 => TimeToTrigger__ms80
  | 4 => TimeToTrigger__ms100
  | 5 => TimeToTrigger__ms128
  | 6 => TimeToTrigger__ms160
  | 7 => TimeToTrigger__ms256
  | 8 => TimeToTrigger__ms320
  | 9 => TimeToTrigger__ms480
  | 10 => TimeToTrigger__ms512
  | 11 => TimeToTrigger__ms640
  | 12 => TimeToTrigger__ms1024
  | 13 => TimeToTrigger__ms1280
  | 14 => TimeToTrigger__ms2560
  | 15 => TimeToTrigger__ms5120
  | _ => TimeToTrigger__ms0
  end.
Lemma TimeToTrigger__F1F2 : forall x : TimeToTrigger__Type, (TimeToTrigger__F1 x <= 15) /\ TimeToTrigger__F2 (TimeToTrigger__F1 x) = x. imp_solve. Qed.
Lemma TimeToTrigger__F2F1 : forall (y : nat) (H : y <= 15), TimeToTrigger__F1 (TimeToTrigger__F2 y) = y. enum_solve H y. Qed.


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
Definition TimeToTrigger__Format : T_Format TimeToTrigger__Type (fun _ => True) :=
(* Eval compute in *) proj3_format TimeToTrigger__nat__Format TimeToTrigger__F1 TimeToTrigger__F2 TimeToTrigger__F1F2 TimeToTrigger__F2F1.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

