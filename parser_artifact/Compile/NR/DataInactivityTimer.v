Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DataInactivityTimer__Type : Set :=
 | DataInactivityTimer__s1
 | DataInactivityTimer__s2
 | DataInactivityTimer__s3
 | DataInactivityTimer__s5
 | DataInactivityTimer__s7
 | DataInactivityTimer__s10
 | DataInactivityTimer__s15
 | DataInactivityTimer__s20
 | DataInactivityTimer__s40
 | DataInactivityTimer__s50
 | DataInactivityTimer__s60
 | DataInactivityTimer__s80
 | DataInactivityTimer__s100
 | DataInactivityTimer__s120
 | DataInactivityTimer__s150
 | DataInactivityTimer__s180
.
Definition DataInactivityTimer__cond := (fun (_ : DataInactivityTimer__Type) => True).
Lemma DataInactivityTimer__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DataInactivityTimer__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 DataInactivityTimer__nat__helper.

Definition DataInactivityTimer__F1 t :=
  match t with
  | DataInactivityTimer__s1 => 0
  | DataInactivityTimer__s2 => 1
  | DataInactivityTimer__s3 => 2
  | DataInactivityTimer__s5 => 3
  | DataInactivityTimer__s7 => 4
  | DataInactivityTimer__s10 => 5
  | DataInactivityTimer__s15 => 6
  | DataInactivityTimer__s20 => 7
  | DataInactivityTimer__s40 => 8
  | DataInactivityTimer__s50 => 9
  | DataInactivityTimer__s60 => 10
  | DataInactivityTimer__s80 => 11
  | DataInactivityTimer__s100 => 12
  | DataInactivityTimer__s120 => 13
  | DataInactivityTimer__s150 => 14
  | DataInactivityTimer__s180 => 15
  end.
Definition DataInactivityTimer__F2 n :=
  match n with
  | 0 => DataInactivityTimer__s1
  | 1 => DataInactivityTimer__s2
  | 2 => DataInactivityTimer__s3
  | 3 => DataInactivityTimer__s5
  | 4 => DataInactivityTimer__s7
  | 5 => DataInactivityTimer__s10
  | 6 => DataInactivityTimer__s15
  | 7 => DataInactivityTimer__s20
  | 8 => DataInactivityTimer__s40
  | 9 => DataInactivityTimer__s50
  | 10 => DataInactivityTimer__s60
  | 11 => DataInactivityTimer__s80
  | 12 => DataInactivityTimer__s100
  | 13 => DataInactivityTimer__s120
  | 14 => DataInactivityTimer__s150
  | 15 => DataInactivityTimer__s180
  | _ => DataInactivityTimer__s1
  end.
Lemma DataInactivityTimer__F1F2 : forall x : DataInactivityTimer__Type, (DataInactivityTimer__F1 x <= 15) /\ DataInactivityTimer__F2 (DataInactivityTimer__F1 x) = x. imp_solve. Qed.
Lemma DataInactivityTimer__F2F1 : forall (y : nat) (H : y <= 15), DataInactivityTimer__F1 (DataInactivityTimer__F2 y) = y. enum_solve H y. Qed.


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
Definition DataInactivityTimer__Format : T_Format DataInactivityTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DataInactivityTimer__nat__Format DataInactivityTimer__F1 DataInactivityTimer__F2 DataInactivityTimer__F1F2 DataInactivityTimer__F2F1.

Opaque DataInactivityTimer__cond DataInactivityTimer__Format.

