Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ReducedAggregatedBandwidth__Type : Set :=
 | ReducedAggregatedBandwidth__mhz0
 | ReducedAggregatedBandwidth__mhz10
 | ReducedAggregatedBandwidth__mhz20
 | ReducedAggregatedBandwidth__mhz30
 | ReducedAggregatedBandwidth__mhz40
 | ReducedAggregatedBandwidth__mhz50
 | ReducedAggregatedBandwidth__mhz60
 | ReducedAggregatedBandwidth__mhz80
 | ReducedAggregatedBandwidth__mhz100
 | ReducedAggregatedBandwidth__mhz200
 | ReducedAggregatedBandwidth__mhz300
 | ReducedAggregatedBandwidth__mhz400
.
Definition ReducedAggregatedBandwidth__cond := (fun (_ : ReducedAggregatedBandwidth__Type) => True).
Lemma ReducedAggregatedBandwidth__nat__helper : to_bit_sz 11 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReducedAggregatedBandwidth__nat__Format : T_Format nat (fun z => (z <= 11)) :=
  nat_enum_format 11 ReducedAggregatedBandwidth__nat__helper.

Definition ReducedAggregatedBandwidth__F1 t :=
  match t with
  | ReducedAggregatedBandwidth__mhz0 => 0
  | ReducedAggregatedBandwidth__mhz10 => 1
  | ReducedAggregatedBandwidth__mhz20 => 2
  | ReducedAggregatedBandwidth__mhz30 => 3
  | ReducedAggregatedBandwidth__mhz40 => 4
  | ReducedAggregatedBandwidth__mhz50 => 5
  | ReducedAggregatedBandwidth__mhz60 => 6
  | ReducedAggregatedBandwidth__mhz80 => 7
  | ReducedAggregatedBandwidth__mhz100 => 8
  | ReducedAggregatedBandwidth__mhz200 => 9
  | ReducedAggregatedBandwidth__mhz300 => 10
  | ReducedAggregatedBandwidth__mhz400 => 11
  end.
Definition ReducedAggregatedBandwidth__F2 n :=
  match n with
  | 0 => ReducedAggregatedBandwidth__mhz0
  | 1 => ReducedAggregatedBandwidth__mhz10
  | 2 => ReducedAggregatedBandwidth__mhz20
  | 3 => ReducedAggregatedBandwidth__mhz30
  | 4 => ReducedAggregatedBandwidth__mhz40
  | 5 => ReducedAggregatedBandwidth__mhz50
  | 6 => ReducedAggregatedBandwidth__mhz60
  | 7 => ReducedAggregatedBandwidth__mhz80
  | 8 => ReducedAggregatedBandwidth__mhz100
  | 9 => ReducedAggregatedBandwidth__mhz200
  | 10 => ReducedAggregatedBandwidth__mhz300
  | 11 => ReducedAggregatedBandwidth__mhz400
  | _ => ReducedAggregatedBandwidth__mhz0
  end.
Lemma ReducedAggregatedBandwidth__F1F2 : forall x : ReducedAggregatedBandwidth__Type, (ReducedAggregatedBandwidth__F1 x <= 11) /\ ReducedAggregatedBandwidth__F2 (ReducedAggregatedBandwidth__F1 x) = x. imp_solve. Qed.
Lemma ReducedAggregatedBandwidth__F2F1 : forall (y : nat) (H : y <= 11), ReducedAggregatedBandwidth__F1 (ReducedAggregatedBandwidth__F2 y) = y. enum_solve H y. Qed.


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
Definition ReducedAggregatedBandwidth__Format : T_Format ReducedAggregatedBandwidth__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReducedAggregatedBandwidth__nat__Format ReducedAggregatedBandwidth__F1 ReducedAggregatedBandwidth__F2 ReducedAggregatedBandwidth__F1F2 ReducedAggregatedBandwidth__F2F1.

Opaque ReducedAggregatedBandwidth__cond ReducedAggregatedBandwidth__Format.

