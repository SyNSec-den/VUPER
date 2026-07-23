Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UL_DataSplitThreshold__Type : Set :=
 | UL_DataSplitThreshold__b0
 | UL_DataSplitThreshold__b100
 | UL_DataSplitThreshold__b200
 | UL_DataSplitThreshold__b400
 | UL_DataSplitThreshold__b800
 | UL_DataSplitThreshold__b1600
 | UL_DataSplitThreshold__b3200
 | UL_DataSplitThreshold__b6400
 | UL_DataSplitThreshold__b12800
 | UL_DataSplitThreshold__b25600
 | UL_DataSplitThreshold__b51200
 | UL_DataSplitThreshold__b102400
 | UL_DataSplitThreshold__b204800
 | UL_DataSplitThreshold__b409600
 | UL_DataSplitThreshold__b819200
 | UL_DataSplitThreshold__b1228800
 | UL_DataSplitThreshold__b1638400
 | UL_DataSplitThreshold__b2457600
 | UL_DataSplitThreshold__b3276800
 | UL_DataSplitThreshold__b4096000
 | UL_DataSplitThreshold__b4915200
 | UL_DataSplitThreshold__b5734400
 | UL_DataSplitThreshold__b6553600
 | UL_DataSplitThreshold__infinity
 | UL_DataSplitThreshold__spare8
 | UL_DataSplitThreshold__spare7
 | UL_DataSplitThreshold__spare6
 | UL_DataSplitThreshold__spare5
 | UL_DataSplitThreshold__spare4
 | UL_DataSplitThreshold__spare3
 | UL_DataSplitThreshold__spare2
 | UL_DataSplitThreshold__spare1
.
Definition UL_DataSplitThreshold__cond := (fun (_ : UL_DataSplitThreshold__Type) => True).
Lemma UL_DataSplitThreshold__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UL_DataSplitThreshold__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 UL_DataSplitThreshold__nat__helper.

Definition UL_DataSplitThreshold__F1 t :=
  match t with
  | UL_DataSplitThreshold__b0 => 0
  | UL_DataSplitThreshold__b100 => 1
  | UL_DataSplitThreshold__b200 => 2
  | UL_DataSplitThreshold__b400 => 3
  | UL_DataSplitThreshold__b800 => 4
  | UL_DataSplitThreshold__b1600 => 5
  | UL_DataSplitThreshold__b3200 => 6
  | UL_DataSplitThreshold__b6400 => 7
  | UL_DataSplitThreshold__b12800 => 8
  | UL_DataSplitThreshold__b25600 => 9
  | UL_DataSplitThreshold__b51200 => 10
  | UL_DataSplitThreshold__b102400 => 11
  | UL_DataSplitThreshold__b204800 => 12
  | UL_DataSplitThreshold__b409600 => 13
  | UL_DataSplitThreshold__b819200 => 14
  | UL_DataSplitThreshold__b1228800 => 15
  | UL_DataSplitThreshold__b1638400 => 16
  | UL_DataSplitThreshold__b2457600 => 17
  | UL_DataSplitThreshold__b3276800 => 18
  | UL_DataSplitThreshold__b4096000 => 19
  | UL_DataSplitThreshold__b4915200 => 20
  | UL_DataSplitThreshold__b5734400 => 21
  | UL_DataSplitThreshold__b6553600 => 22
  | UL_DataSplitThreshold__infinity => 23
  | UL_DataSplitThreshold__spare8 => 24
  | UL_DataSplitThreshold__spare7 => 25
  | UL_DataSplitThreshold__spare6 => 26
  | UL_DataSplitThreshold__spare5 => 27
  | UL_DataSplitThreshold__spare4 => 28
  | UL_DataSplitThreshold__spare3 => 29
  | UL_DataSplitThreshold__spare2 => 30
  | UL_DataSplitThreshold__spare1 => 31
  end.
Definition UL_DataSplitThreshold__F2 n :=
  match n with
  | 0 => UL_DataSplitThreshold__b0
  | 1 => UL_DataSplitThreshold__b100
  | 2 => UL_DataSplitThreshold__b200
  | 3 => UL_DataSplitThreshold__b400
  | 4 => UL_DataSplitThreshold__b800
  | 5 => UL_DataSplitThreshold__b1600
  | 6 => UL_DataSplitThreshold__b3200
  | 7 => UL_DataSplitThreshold__b6400
  | 8 => UL_DataSplitThreshold__b12800
  | 9 => UL_DataSplitThreshold__b25600
  | 10 => UL_DataSplitThreshold__b51200
  | 11 => UL_DataSplitThreshold__b102400
  | 12 => UL_DataSplitThreshold__b204800
  | 13 => UL_DataSplitThreshold__b409600
  | 14 => UL_DataSplitThreshold__b819200
  | 15 => UL_DataSplitThreshold__b1228800
  | 16 => UL_DataSplitThreshold__b1638400
  | 17 => UL_DataSplitThreshold__b2457600
  | 18 => UL_DataSplitThreshold__b3276800
  | 19 => UL_DataSplitThreshold__b4096000
  | 20 => UL_DataSplitThreshold__b4915200
  | 21 => UL_DataSplitThreshold__b5734400
  | 22 => UL_DataSplitThreshold__b6553600
  | 23 => UL_DataSplitThreshold__infinity
  | 24 => UL_DataSplitThreshold__spare8
  | 25 => UL_DataSplitThreshold__spare7
  | 26 => UL_DataSplitThreshold__spare6
  | 27 => UL_DataSplitThreshold__spare5
  | 28 => UL_DataSplitThreshold__spare4
  | 29 => UL_DataSplitThreshold__spare3
  | 30 => UL_DataSplitThreshold__spare2
  | 31 => UL_DataSplitThreshold__spare1
  | _ => UL_DataSplitThreshold__b0
  end.
Lemma UL_DataSplitThreshold__F1F2 : forall x : UL_DataSplitThreshold__Type, (UL_DataSplitThreshold__F1 x <= 31) /\ UL_DataSplitThreshold__F2 (UL_DataSplitThreshold__F1 x) = x. imp_solve. Qed.
Lemma UL_DataSplitThreshold__F2F1 : forall (y : nat) (H : y <= 31), UL_DataSplitThreshold__F1 (UL_DataSplitThreshold__F2 y) = y. enum_solve H y. Qed.


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
Definition UL_DataSplitThreshold__Format : T_Format UL_DataSplitThreshold__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UL_DataSplitThreshold__nat__Format UL_DataSplitThreshold__F1 UL_DataSplitThreshold__F2 UL_DataSplitThreshold__F1F2 UL_DataSplitThreshold__F2F1.

Opaque UL_DataSplitThreshold__cond UL_DataSplitThreshold__Format.

