Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Inductive T_Offset_r16__Type : Set :=
 | T_Offset_r16__ms0dot5
 | T_Offset_r16__ms0dot75
 | T_Offset_r16__ms1
 | T_Offset_r16__ms1dot5
 | T_Offset_r16__ms2
 | T_Offset_r16__ms2dot5
 | T_Offset_r16__ms3
 | T_Offset_r16__spare1
.
Definition T_Offset_r16__cond := (fun (_ : T_Offset_r16__Type) => True).
Lemma T_Offset_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition T_Offset_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 T_Offset_r16__nat__helper.

Definition T_Offset_r16__F1 t :=
  match t with
  | T_Offset_r16__ms0dot5 => 0
  | T_Offset_r16__ms0dot75 => 1
  | T_Offset_r16__ms1 => 2
  | T_Offset_r16__ms1dot5 => 3
  | T_Offset_r16__ms2 => 4
  | T_Offset_r16__ms2dot5 => 5
  | T_Offset_r16__ms3 => 6
  | T_Offset_r16__spare1 => 7
  end.
Definition T_Offset_r16__F2 n :=
  match n with
  | 0 => T_Offset_r16__ms0dot5
  | 1 => T_Offset_r16__ms0dot75
  | 2 => T_Offset_r16__ms1
  | 3 => T_Offset_r16__ms1dot5
  | 4 => T_Offset_r16__ms2
  | 5 => T_Offset_r16__ms2dot5
  | 6 => T_Offset_r16__ms3
  | 7 => T_Offset_r16__spare1
  | _ => T_Offset_r16__ms0dot5
  end.
Lemma T_Offset_r16__F1F2 : forall x : T_Offset_r16__Type, (T_Offset_r16__F1 x <= 7) /\ T_Offset_r16__F2 (T_Offset_r16__F1 x) = x. imp_solve. Qed.
Lemma T_Offset_r16__F2F1 : forall (y : nat) (H : y <= 7), T_Offset_r16__F1 (T_Offset_r16__F2 y) = y. enum_solve H y. Qed.


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
Definition T_Offset_r16__Format : T_Format T_Offset_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format T_Offset_r16__nat__Format T_Offset_r16__F1 T_Offset_r16__F2 T_Offset_r16__F1F2 T_Offset_r16__F2F1.

Opaque T_Offset_r16__cond T_Offset_r16__Format.

