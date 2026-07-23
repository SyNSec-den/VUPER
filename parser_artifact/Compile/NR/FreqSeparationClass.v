Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FreqSeparationClass__root__Type : Set :=
 | FreqSeparationClass__root__mhz800
 | FreqSeparationClass__root__mhz1200
 | FreqSeparationClass__root__mhz1400
.
Definition FreqSeparationClass__root__cond := (fun (_ : FreqSeparationClass__root__Type) => True).
Lemma FreqSeparationClass__root__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FreqSeparationClass__root__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FreqSeparationClass__root__nat__helper.

Definition FreqSeparationClass__root__F1 t :=
  match t with
  | FreqSeparationClass__root__mhz800 => 0
  | FreqSeparationClass__root__mhz1200 => 1
  | FreqSeparationClass__root__mhz1400 => 2
  end.
Definition FreqSeparationClass__root__F2 n :=
  match n with
  | 0 => FreqSeparationClass__root__mhz800
  | 1 => FreqSeparationClass__root__mhz1200
  | 2 => FreqSeparationClass__root__mhz1400
  | _ => FreqSeparationClass__root__mhz800
  end.
Lemma FreqSeparationClass__root__F1F2 : forall x : FreqSeparationClass__root__Type, (FreqSeparationClass__root__F1 x <= 2) /\ FreqSeparationClass__root__F2 (FreqSeparationClass__root__F1 x) = x. imp_solve. Qed.
Lemma FreqSeparationClass__root__F2F1 : forall (y : nat) (H : y <= 2), FreqSeparationClass__root__F1 (FreqSeparationClass__root__F2 y) = y. enum_solve H y. Qed.

Inductive FreqSeparationClass__ext__Type : Set :=
 | FreqSeparationClass__ext__mhz400_v1650
 | FreqSeparationClass__ext__mhz600_v1650
.
Definition FreqSeparationClass__ext__cond := (fun (_ : FreqSeparationClass__ext__Type) => True).
Lemma FreqSeparationClass__ext__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FreqSeparationClass__ext__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 FreqSeparationClass__ext__nat__helper.

Definition FreqSeparationClass__ext__F1 t :=
  match t with
  | FreqSeparationClass__ext__mhz400_v1650 => 0
  | FreqSeparationClass__ext__mhz600_v1650 => 1
  end.
Definition FreqSeparationClass__ext__F2 n :=
  match n with
  | 0 => FreqSeparationClass__ext__mhz400_v1650
  | 1 => FreqSeparationClass__ext__mhz600_v1650
  | _ => FreqSeparationClass__ext__mhz400_v1650
  end.
Lemma FreqSeparationClass__ext__F1F2 : forall x : FreqSeparationClass__ext__Type, (FreqSeparationClass__ext__F1 x <= 1) /\ FreqSeparationClass__ext__F2 (FreqSeparationClass__ext__F1 x) = x. imp_solve. Qed.
Lemma FreqSeparationClass__ext__F2F1 : forall (y : nat) (H : y <= 1), FreqSeparationClass__ext__F1 (FreqSeparationClass__ext__F2 y) = y. enum_solve H y. Qed.

Lemma FreqSeparationClass__ext__helper1 : forall a, a <= 1 -> a <= 63. lia. Qed.
Definition FreqSeparationClass__ext__helper_format : T_Format nat (fun n => n <= 1) :=
            restrict_format (fun n : nat => n <= 1)
                  small_integer_format
                  FreqSeparationClass__ext__helper1
                  (fun a => Compare_dec.le_dec a 1).
Definition FreqSeparationClass__Type : Set := FreqSeparationClass__root__Type + FreqSeparationClass__ext__Type.
Definition FreqSeparationClass__cond := sum_cond FreqSeparationClass__root__cond FreqSeparationClass__ext__cond.


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
Definition FreqSeparationClass__root__Format : T_Format FreqSeparationClass__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format FreqSeparationClass__root__nat__Format FreqSeparationClass__root__F1 FreqSeparationClass__root__F2 FreqSeparationClass__root__F1F2 FreqSeparationClass__root__F2F1.

Opaque FreqSeparationClass__root__cond FreqSeparationClass__root__Format.

Definition FreqSeparationClass__ext__Format : T_Format FreqSeparationClass__ext__Type FreqSeparationClass__ext__cond :=
proj3_format FreqSeparationClass__ext__helper_format FreqSeparationClass__ext__F1 FreqSeparationClass__ext__F2 FreqSeparationClass__ext__F1F2 FreqSeparationClass__ext__F2F1.

Opaque FreqSeparationClass__ext__cond FreqSeparationClass__ext__Format.

Definition FreqSeparationClass__Format : T_Format FreqSeparationClass__Type FreqSeparationClass__cond := sum_format FreqSeparationClass__root__Format FreqSeparationClass__ext__Format.
Opaque FreqSeparationClass__cond FreqSeparationClass__Format.

Opaque FreqSeparationClass__cond FreqSeparationClass__Format.

