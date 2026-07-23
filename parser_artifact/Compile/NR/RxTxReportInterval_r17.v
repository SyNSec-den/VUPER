Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RxTxReportInterval_r17__Type : Set :=
 | RxTxReportInterval_r17__ms80
 | RxTxReportInterval_r17__ms120
 | RxTxReportInterval_r17__ms160
 | RxTxReportInterval_r17__ms240
 | RxTxReportInterval_r17__ms320
 | RxTxReportInterval_r17__ms480
 | RxTxReportInterval_r17__ms640
 | RxTxReportInterval_r17__ms1024
 | RxTxReportInterval_r17__ms1280
 | RxTxReportInterval_r17__ms2048
 | RxTxReportInterval_r17__ms2560
 | RxTxReportInterval_r17__ms5120
 | RxTxReportInterval_r17__spare4
 | RxTxReportInterval_r17__spare3
 | RxTxReportInterval_r17__spare2
 | RxTxReportInterval_r17__spare1
.
Definition RxTxReportInterval_r17__cond := (fun (_ : RxTxReportInterval_r17__Type) => True).
Lemma RxTxReportInterval_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RxTxReportInterval_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 RxTxReportInterval_r17__nat__helper.

Definition RxTxReportInterval_r17__F1 t :=
  match t with
  | RxTxReportInterval_r17__ms80 => 0
  | RxTxReportInterval_r17__ms120 => 1
  | RxTxReportInterval_r17__ms160 => 2
  | RxTxReportInterval_r17__ms240 => 3
  | RxTxReportInterval_r17__ms320 => 4
  | RxTxReportInterval_r17__ms480 => 5
  | RxTxReportInterval_r17__ms640 => 6
  | RxTxReportInterval_r17__ms1024 => 7
  | RxTxReportInterval_r17__ms1280 => 8
  | RxTxReportInterval_r17__ms2048 => 9
  | RxTxReportInterval_r17__ms2560 => 10
  | RxTxReportInterval_r17__ms5120 => 11
  | RxTxReportInterval_r17__spare4 => 12
  | RxTxReportInterval_r17__spare3 => 13
  | RxTxReportInterval_r17__spare2 => 14
  | RxTxReportInterval_r17__spare1 => 15
  end.
Definition RxTxReportInterval_r17__F2 n :=
  match n with
  | 0 => RxTxReportInterval_r17__ms80
  | 1 => RxTxReportInterval_r17__ms120
  | 2 => RxTxReportInterval_r17__ms160
  | 3 => RxTxReportInterval_r17__ms240
  | 4 => RxTxReportInterval_r17__ms320
  | 5 => RxTxReportInterval_r17__ms480
  | 6 => RxTxReportInterval_r17__ms640
  | 7 => RxTxReportInterval_r17__ms1024
  | 8 => RxTxReportInterval_r17__ms1280
  | 9 => RxTxReportInterval_r17__ms2048
  | 10 => RxTxReportInterval_r17__ms2560
  | 11 => RxTxReportInterval_r17__ms5120
  | 12 => RxTxReportInterval_r17__spare4
  | 13 => RxTxReportInterval_r17__spare3
  | 14 => RxTxReportInterval_r17__spare2
  | 15 => RxTxReportInterval_r17__spare1
  | _ => RxTxReportInterval_r17__ms80
  end.
Lemma RxTxReportInterval_r17__F1F2 : forall x : RxTxReportInterval_r17__Type, (RxTxReportInterval_r17__F1 x <= 15) /\ RxTxReportInterval_r17__F2 (RxTxReportInterval_r17__F1 x) = x. imp_solve. Qed.
Lemma RxTxReportInterval_r17__F2F1 : forall (y : nat) (H : y <= 15), RxTxReportInterval_r17__F1 (RxTxReportInterval_r17__F2 y) = y. enum_solve H y. Qed.


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
Definition RxTxReportInterval_r17__Format : T_Format RxTxReportInterval_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RxTxReportInterval_r17__nat__Format RxTxReportInterval_r17__F1 RxTxReportInterval_r17__F2 RxTxReportInterval_r17__F1F2 RxTxReportInterval_r17__F2F1.

Opaque RxTxReportInterval_r17__cond RxTxReportInterval_r17__Format.

