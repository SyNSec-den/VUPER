Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive EUTRA_AllowedMeasBandwidth__Type : Set :=
 | EUTRA_AllowedMeasBandwidth__mbw6
 | EUTRA_AllowedMeasBandwidth__mbw15
 | EUTRA_AllowedMeasBandwidth__mbw25
 | EUTRA_AllowedMeasBandwidth__mbw50
 | EUTRA_AllowedMeasBandwidth__mbw75
 | EUTRA_AllowedMeasBandwidth__mbw100
.
Definition EUTRA_AllowedMeasBandwidth__cond := (fun (_ : EUTRA_AllowedMeasBandwidth__Type) => True).
Lemma EUTRA_AllowedMeasBandwidth__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_AllowedMeasBandwidth__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 EUTRA_AllowedMeasBandwidth__nat__helper.

Definition EUTRA_AllowedMeasBandwidth__F1 t :=
  match t with
  | EUTRA_AllowedMeasBandwidth__mbw6 => 0
  | EUTRA_AllowedMeasBandwidth__mbw15 => 1
  | EUTRA_AllowedMeasBandwidth__mbw25 => 2
  | EUTRA_AllowedMeasBandwidth__mbw50 => 3
  | EUTRA_AllowedMeasBandwidth__mbw75 => 4
  | EUTRA_AllowedMeasBandwidth__mbw100 => 5
  end.
Definition EUTRA_AllowedMeasBandwidth__F2 n :=
  match n with
  | 0 => EUTRA_AllowedMeasBandwidth__mbw6
  | 1 => EUTRA_AllowedMeasBandwidth__mbw15
  | 2 => EUTRA_AllowedMeasBandwidth__mbw25
  | 3 => EUTRA_AllowedMeasBandwidth__mbw50
  | 4 => EUTRA_AllowedMeasBandwidth__mbw75
  | 5 => EUTRA_AllowedMeasBandwidth__mbw100
  | _ => EUTRA_AllowedMeasBandwidth__mbw6
  end.
Lemma EUTRA_AllowedMeasBandwidth__F1F2 : forall x : EUTRA_AllowedMeasBandwidth__Type, (EUTRA_AllowedMeasBandwidth__F1 x <= 5) /\ EUTRA_AllowedMeasBandwidth__F2 (EUTRA_AllowedMeasBandwidth__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_AllowedMeasBandwidth__F2F1 : forall (y : nat) (H : y <= 5), EUTRA_AllowedMeasBandwidth__F1 (EUTRA_AllowedMeasBandwidth__F2 y) = y. enum_solve H y. Qed.


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
Definition EUTRA_AllowedMeasBandwidth__Format : T_Format EUTRA_AllowedMeasBandwidth__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_AllowedMeasBandwidth__nat__Format EUTRA_AllowedMeasBandwidth__F1 EUTRA_AllowedMeasBandwidth__F2 EUTRA_AllowedMeasBandwidth__F1F2 EUTRA_AllowedMeasBandwidth__F2F1.

Opaque EUTRA_AllowedMeasBandwidth__cond EUTRA_AllowedMeasBandwidth__Format.

