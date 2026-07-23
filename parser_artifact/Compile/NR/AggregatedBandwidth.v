Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive AggregatedBandwidth__Type : Set :=
 | AggregatedBandwidth__mhz50
 | AggregatedBandwidth__mhz100
 | AggregatedBandwidth__mhz150
 | AggregatedBandwidth__mhz200
 | AggregatedBandwidth__mhz250
 | AggregatedBandwidth__mhz300
 | AggregatedBandwidth__mhz350
 | AggregatedBandwidth__mhz400
 | AggregatedBandwidth__mhz450
 | AggregatedBandwidth__mhz500
 | AggregatedBandwidth__mhz550
 | AggregatedBandwidth__mhz600
 | AggregatedBandwidth__mhz650
 | AggregatedBandwidth__mhz700
 | AggregatedBandwidth__mhz750
 | AggregatedBandwidth__mhz800
.
Definition AggregatedBandwidth__cond := (fun (_ : AggregatedBandwidth__Type) => True).
Lemma AggregatedBandwidth__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition AggregatedBandwidth__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 AggregatedBandwidth__nat__helper.

Definition AggregatedBandwidth__F1 t :=
  match t with
  | AggregatedBandwidth__mhz50 => 0
  | AggregatedBandwidth__mhz100 => 1
  | AggregatedBandwidth__mhz150 => 2
  | AggregatedBandwidth__mhz200 => 3
  | AggregatedBandwidth__mhz250 => 4
  | AggregatedBandwidth__mhz300 => 5
  | AggregatedBandwidth__mhz350 => 6
  | AggregatedBandwidth__mhz400 => 7
  | AggregatedBandwidth__mhz450 => 8
  | AggregatedBandwidth__mhz500 => 9
  | AggregatedBandwidth__mhz550 => 10
  | AggregatedBandwidth__mhz600 => 11
  | AggregatedBandwidth__mhz650 => 12
  | AggregatedBandwidth__mhz700 => 13
  | AggregatedBandwidth__mhz750 => 14
  | AggregatedBandwidth__mhz800 => 15
  end.
Definition AggregatedBandwidth__F2 n :=
  match n with
  | 0 => AggregatedBandwidth__mhz50
  | 1 => AggregatedBandwidth__mhz100
  | 2 => AggregatedBandwidth__mhz150
  | 3 => AggregatedBandwidth__mhz200
  | 4 => AggregatedBandwidth__mhz250
  | 5 => AggregatedBandwidth__mhz300
  | 6 => AggregatedBandwidth__mhz350
  | 7 => AggregatedBandwidth__mhz400
  | 8 => AggregatedBandwidth__mhz450
  | 9 => AggregatedBandwidth__mhz500
  | 10 => AggregatedBandwidth__mhz550
  | 11 => AggregatedBandwidth__mhz600
  | 12 => AggregatedBandwidth__mhz650
  | 13 => AggregatedBandwidth__mhz700
  | 14 => AggregatedBandwidth__mhz750
  | 15 => AggregatedBandwidth__mhz800
  | _ => AggregatedBandwidth__mhz50
  end.
Lemma AggregatedBandwidth__F1F2 : forall x : AggregatedBandwidth__Type, (AggregatedBandwidth__F1 x <= 15) /\ AggregatedBandwidth__F2 (AggregatedBandwidth__F1 x) = x. imp_solve. Qed.
Lemma AggregatedBandwidth__F2F1 : forall (y : nat) (H : y <= 15), AggregatedBandwidth__F1 (AggregatedBandwidth__F2 y) = y. enum_solve H y. Qed.


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
Definition AggregatedBandwidth__Format : T_Format AggregatedBandwidth__Type (fun _ => True) :=
(* Eval compute in *) proj3_format AggregatedBandwidth__nat__Format AggregatedBandwidth__F1 AggregatedBandwidth__F2 AggregatedBandwidth__F1F2 AggregatedBandwidth__F2F1.

Opaque AggregatedBandwidth__cond AggregatedBandwidth__Format.

