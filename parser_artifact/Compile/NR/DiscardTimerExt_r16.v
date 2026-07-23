Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DiscardTimerExt_r16__Type : Set :=
 | DiscardTimerExt_r16__ms0dot5
 | DiscardTimerExt_r16__ms1
 | DiscardTimerExt_r16__ms2
 | DiscardTimerExt_r16__ms4
 | DiscardTimerExt_r16__ms6
 | DiscardTimerExt_r16__ms8
 | DiscardTimerExt_r16__spare2
 | DiscardTimerExt_r16__spare1
.
Definition DiscardTimerExt_r16__cond := (fun (_ : DiscardTimerExt_r16__Type) => True).
Lemma DiscardTimerExt_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DiscardTimerExt_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 DiscardTimerExt_r16__nat__helper.

Definition DiscardTimerExt_r16__F1 t :=
  match t with
  | DiscardTimerExt_r16__ms0dot5 => 0
  | DiscardTimerExt_r16__ms1 => 1
  | DiscardTimerExt_r16__ms2 => 2
  | DiscardTimerExt_r16__ms4 => 3
  | DiscardTimerExt_r16__ms6 => 4
  | DiscardTimerExt_r16__ms8 => 5
  | DiscardTimerExt_r16__spare2 => 6
  | DiscardTimerExt_r16__spare1 => 7
  end.
Definition DiscardTimerExt_r16__F2 n :=
  match n with
  | 0 => DiscardTimerExt_r16__ms0dot5
  | 1 => DiscardTimerExt_r16__ms1
  | 2 => DiscardTimerExt_r16__ms2
  | 3 => DiscardTimerExt_r16__ms4
  | 4 => DiscardTimerExt_r16__ms6
  | 5 => DiscardTimerExt_r16__ms8
  | 6 => DiscardTimerExt_r16__spare2
  | 7 => DiscardTimerExt_r16__spare1
  | _ => DiscardTimerExt_r16__ms0dot5
  end.
Lemma DiscardTimerExt_r16__F1F2 : forall x : DiscardTimerExt_r16__Type, (DiscardTimerExt_r16__F1 x <= 7) /\ DiscardTimerExt_r16__F2 (DiscardTimerExt_r16__F1 x) = x. imp_solve. Qed.
Lemma DiscardTimerExt_r16__F2F1 : forall (y : nat) (H : y <= 7), DiscardTimerExt_r16__F1 (DiscardTimerExt_r16__F2 y) = y. enum_solve H y. Qed.


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
Definition DiscardTimerExt_r16__Format : T_Format DiscardTimerExt_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DiscardTimerExt_r16__nat__Format DiscardTimerExt_r16__F1 DiscardTimerExt_r16__F2 DiscardTimerExt_r16__F1F2 DiscardTimerExt_r16__F2F1.

Opaque DiscardTimerExt_r16__cond DiscardTimerExt_r16__Format.

