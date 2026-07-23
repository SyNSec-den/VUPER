Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SupportedBandUTRA_FDD_r16__Type : Set :=
 | SupportedBandUTRA_FDD_r16__bandI
 | SupportedBandUTRA_FDD_r16__bandII
 | SupportedBandUTRA_FDD_r16__bandIII
 | SupportedBandUTRA_FDD_r16__bandIV
 | SupportedBandUTRA_FDD_r16__bandV
 | SupportedBandUTRA_FDD_r16__bandVI
 | SupportedBandUTRA_FDD_r16__bandVII
 | SupportedBandUTRA_FDD_r16__bandVIII
 | SupportedBandUTRA_FDD_r16__bandIX
 | SupportedBandUTRA_FDD_r16__bandX
 | SupportedBandUTRA_FDD_r16__bandXI
 | SupportedBandUTRA_FDD_r16__bandXII
 | SupportedBandUTRA_FDD_r16__bandXIII
 | SupportedBandUTRA_FDD_r16__bandXIV
 | SupportedBandUTRA_FDD_r16__bandXV
 | SupportedBandUTRA_FDD_r16__bandXVI
 | SupportedBandUTRA_FDD_r16__bandXVII
 | SupportedBandUTRA_FDD_r16__bandXVIII
 | SupportedBandUTRA_FDD_r16__bandXIX
 | SupportedBandUTRA_FDD_r16__bandXX
 | SupportedBandUTRA_FDD_r16__bandXXI
 | SupportedBandUTRA_FDD_r16__bandXXII
 | SupportedBandUTRA_FDD_r16__bandXXIII
 | SupportedBandUTRA_FDD_r16__bandXXIV
 | SupportedBandUTRA_FDD_r16__bandXXV
 | SupportedBandUTRA_FDD_r16__bandXXVI
 | SupportedBandUTRA_FDD_r16__bandXXVII
 | SupportedBandUTRA_FDD_r16__bandXXVIII
 | SupportedBandUTRA_FDD_r16__bandXXIX
 | SupportedBandUTRA_FDD_r16__bandXXX
 | SupportedBandUTRA_FDD_r16__bandXXXI
 | SupportedBandUTRA_FDD_r16__bandXXXII
.
Definition SupportedBandUTRA_FDD_r16__cond := (fun (_ : SupportedBandUTRA_FDD_r16__Type) => True).
Lemma SupportedBandUTRA_FDD_r16__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SupportedBandUTRA_FDD_r16__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SupportedBandUTRA_FDD_r16__nat__helper.

Definition SupportedBandUTRA_FDD_r16__F1 t :=
  match t with
  | SupportedBandUTRA_FDD_r16__bandI => 0
  | SupportedBandUTRA_FDD_r16__bandII => 1
  | SupportedBandUTRA_FDD_r16__bandIII => 2
  | SupportedBandUTRA_FDD_r16__bandIV => 3
  | SupportedBandUTRA_FDD_r16__bandV => 4
  | SupportedBandUTRA_FDD_r16__bandVI => 5
  | SupportedBandUTRA_FDD_r16__bandVII => 6
  | SupportedBandUTRA_FDD_r16__bandVIII => 7
  | SupportedBandUTRA_FDD_r16__bandIX => 8
  | SupportedBandUTRA_FDD_r16__bandX => 9
  | SupportedBandUTRA_FDD_r16__bandXI => 10
  | SupportedBandUTRA_FDD_r16__bandXII => 11
  | SupportedBandUTRA_FDD_r16__bandXIII => 12
  | SupportedBandUTRA_FDD_r16__bandXIV => 13
  | SupportedBandUTRA_FDD_r16__bandXV => 14
  | SupportedBandUTRA_FDD_r16__bandXVI => 15
  | SupportedBandUTRA_FDD_r16__bandXVII => 16
  | SupportedBandUTRA_FDD_r16__bandXVIII => 17
  | SupportedBandUTRA_FDD_r16__bandXIX => 18
  | SupportedBandUTRA_FDD_r16__bandXX => 19
  | SupportedBandUTRA_FDD_r16__bandXXI => 20
  | SupportedBandUTRA_FDD_r16__bandXXII => 21
  | SupportedBandUTRA_FDD_r16__bandXXIII => 22
  | SupportedBandUTRA_FDD_r16__bandXXIV => 23
  | SupportedBandUTRA_FDD_r16__bandXXV => 24
  | SupportedBandUTRA_FDD_r16__bandXXVI => 25
  | SupportedBandUTRA_FDD_r16__bandXXVII => 26
  | SupportedBandUTRA_FDD_r16__bandXXVIII => 27
  | SupportedBandUTRA_FDD_r16__bandXXIX => 28
  | SupportedBandUTRA_FDD_r16__bandXXX => 29
  | SupportedBandUTRA_FDD_r16__bandXXXI => 30
  | SupportedBandUTRA_FDD_r16__bandXXXII => 31
  end.
Definition SupportedBandUTRA_FDD_r16__F2 n :=
  match n with
  | 0 => SupportedBandUTRA_FDD_r16__bandI
  | 1 => SupportedBandUTRA_FDD_r16__bandII
  | 2 => SupportedBandUTRA_FDD_r16__bandIII
  | 3 => SupportedBandUTRA_FDD_r16__bandIV
  | 4 => SupportedBandUTRA_FDD_r16__bandV
  | 5 => SupportedBandUTRA_FDD_r16__bandVI
  | 6 => SupportedBandUTRA_FDD_r16__bandVII
  | 7 => SupportedBandUTRA_FDD_r16__bandVIII
  | 8 => SupportedBandUTRA_FDD_r16__bandIX
  | 9 => SupportedBandUTRA_FDD_r16__bandX
  | 10 => SupportedBandUTRA_FDD_r16__bandXI
  | 11 => SupportedBandUTRA_FDD_r16__bandXII
  | 12 => SupportedBandUTRA_FDD_r16__bandXIII
  | 13 => SupportedBandUTRA_FDD_r16__bandXIV
  | 14 => SupportedBandUTRA_FDD_r16__bandXV
  | 15 => SupportedBandUTRA_FDD_r16__bandXVI
  | 16 => SupportedBandUTRA_FDD_r16__bandXVII
  | 17 => SupportedBandUTRA_FDD_r16__bandXVIII
  | 18 => SupportedBandUTRA_FDD_r16__bandXIX
  | 19 => SupportedBandUTRA_FDD_r16__bandXX
  | 20 => SupportedBandUTRA_FDD_r16__bandXXI
  | 21 => SupportedBandUTRA_FDD_r16__bandXXII
  | 22 => SupportedBandUTRA_FDD_r16__bandXXIII
  | 23 => SupportedBandUTRA_FDD_r16__bandXXIV
  | 24 => SupportedBandUTRA_FDD_r16__bandXXV
  | 25 => SupportedBandUTRA_FDD_r16__bandXXVI
  | 26 => SupportedBandUTRA_FDD_r16__bandXXVII
  | 27 => SupportedBandUTRA_FDD_r16__bandXXVIII
  | 28 => SupportedBandUTRA_FDD_r16__bandXXIX
  | 29 => SupportedBandUTRA_FDD_r16__bandXXX
  | 30 => SupportedBandUTRA_FDD_r16__bandXXXI
  | 31 => SupportedBandUTRA_FDD_r16__bandXXXII
  | _ => SupportedBandUTRA_FDD_r16__bandI
  end.
Lemma SupportedBandUTRA_FDD_r16__F1F2 : forall x : SupportedBandUTRA_FDD_r16__Type, (SupportedBandUTRA_FDD_r16__F1 x <= 31) /\ SupportedBandUTRA_FDD_r16__F2 (SupportedBandUTRA_FDD_r16__F1 x) = x. imp_solve. Qed.
Lemma SupportedBandUTRA_FDD_r16__F2F1 : forall (y : nat) (H : y <= 31), SupportedBandUTRA_FDD_r16__F1 (SupportedBandUTRA_FDD_r16__F2 y) = y. enum_solve H y. Qed.


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
Definition SupportedBandUTRA_FDD_r16__Format : T_Format SupportedBandUTRA_FDD_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SupportedBandUTRA_FDD_r16__nat__Format SupportedBandUTRA_FDD_r16__F1 SupportedBandUTRA_FDD_r16__F2 SupportedBandUTRA_FDD_r16__F1F2 SupportedBandUTRA_FDD_r16__F2F1.

Opaque SupportedBandUTRA_FDD_r16__cond SupportedBandUTRA_FDD_r16__Format.

