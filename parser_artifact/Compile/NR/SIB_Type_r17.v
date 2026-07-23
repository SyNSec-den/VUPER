Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SIB_Type_r17__Type : Set :=
 | SIB_Type_r17__sibType2
 | SIB_Type_r17__sibType3
 | SIB_Type_r17__sibType4
 | SIB_Type_r17__sibType5
 | SIB_Type_r17__sibType9
 | SIB_Type_r17__sibType10_v1610
 | SIB_Type_r17__sibType11_v1610
 | SIB_Type_r17__sibType12_v1610
 | SIB_Type_r17__sibType13_v1610
 | SIB_Type_r17__sibType14_v1610
 | SIB_Type_r17__spare6
 | SIB_Type_r17__spare5
 | SIB_Type_r17__spare4
 | SIB_Type_r17__spare3
 | SIB_Type_r17__spare2
 | SIB_Type_r17__spare1
.
Definition SIB_Type_r17__cond := (fun (_ : SIB_Type_r17__Type) => True).
Lemma SIB_Type_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB_Type_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SIB_Type_r17__nat__helper.

Definition SIB_Type_r17__F1 t :=
  match t with
  | SIB_Type_r17__sibType2 => 0
  | SIB_Type_r17__sibType3 => 1
  | SIB_Type_r17__sibType4 => 2
  | SIB_Type_r17__sibType5 => 3
  | SIB_Type_r17__sibType9 => 4
  | SIB_Type_r17__sibType10_v1610 => 5
  | SIB_Type_r17__sibType11_v1610 => 6
  | SIB_Type_r17__sibType12_v1610 => 7
  | SIB_Type_r17__sibType13_v1610 => 8
  | SIB_Type_r17__sibType14_v1610 => 9
  | SIB_Type_r17__spare6 => 10
  | SIB_Type_r17__spare5 => 11
  | SIB_Type_r17__spare4 => 12
  | SIB_Type_r17__spare3 => 13
  | SIB_Type_r17__spare2 => 14
  | SIB_Type_r17__spare1 => 15
  end.
Definition SIB_Type_r17__F2 n :=
  match n with
  | 0 => SIB_Type_r17__sibType2
  | 1 => SIB_Type_r17__sibType3
  | 2 => SIB_Type_r17__sibType4
  | 3 => SIB_Type_r17__sibType5
  | 4 => SIB_Type_r17__sibType9
  | 5 => SIB_Type_r17__sibType10_v1610
  | 6 => SIB_Type_r17__sibType11_v1610
  | 7 => SIB_Type_r17__sibType12_v1610
  | 8 => SIB_Type_r17__sibType13_v1610
  | 9 => SIB_Type_r17__sibType14_v1610
  | 10 => SIB_Type_r17__spare6
  | 11 => SIB_Type_r17__spare5
  | 12 => SIB_Type_r17__spare4
  | 13 => SIB_Type_r17__spare3
  | 14 => SIB_Type_r17__spare2
  | 15 => SIB_Type_r17__spare1
  | _ => SIB_Type_r17__sibType2
  end.
Lemma SIB_Type_r17__F1F2 : forall x : SIB_Type_r17__Type, (SIB_Type_r17__F1 x <= 15) /\ SIB_Type_r17__F2 (SIB_Type_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB_Type_r17__F2F1 : forall (y : nat) (H : y <= 15), SIB_Type_r17__F1 (SIB_Type_r17__F2 y) = y. enum_solve H y. Qed.


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
Definition SIB_Type_r17__Format : T_Format SIB_Type_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB_Type_r17__nat__Format SIB_Type_r17__F1 SIB_Type_r17__F2 SIB_Type_r17__F1F2 SIB_Type_r17__F2F1.

Opaque SIB_Type_r17__cond SIB_Type_r17__Format.

