Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FrequencyComponent_r17__Type : Set :=
 | FrequencyComponent_r17__activeCarrier
 | FrequencyComponent_r17__configuredCarrier
 | FrequencyComponent_r17__activeBWP
 | FrequencyComponent_r17__configuredBWP
.
Definition FrequencyComponent_r17__cond := (fun (_ : FrequencyComponent_r17__Type) => True).
Lemma FrequencyComponent_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FrequencyComponent_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 FrequencyComponent_r17__nat__helper.

Definition FrequencyComponent_r17__F1 t :=
  match t with
  | FrequencyComponent_r17__activeCarrier => 0
  | FrequencyComponent_r17__configuredCarrier => 1
  | FrequencyComponent_r17__activeBWP => 2
  | FrequencyComponent_r17__configuredBWP => 3
  end.
Definition FrequencyComponent_r17__F2 n :=
  match n with
  | 0 => FrequencyComponent_r17__activeCarrier
  | 1 => FrequencyComponent_r17__configuredCarrier
  | 2 => FrequencyComponent_r17__activeBWP
  | 3 => FrequencyComponent_r17__configuredBWP
  | _ => FrequencyComponent_r17__activeCarrier
  end.
Lemma FrequencyComponent_r17__F1F2 : forall x : FrequencyComponent_r17__Type, (FrequencyComponent_r17__F1 x <= 3) /\ FrequencyComponent_r17__F2 (FrequencyComponent_r17__F1 x) = x. imp_solve. Qed.
Lemma FrequencyComponent_r17__F2F1 : forall (y : nat) (H : y <= 3), FrequencyComponent_r17__F1 (FrequencyComponent_r17__F2 y) = y. enum_solve H y. Qed.


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
Definition FrequencyComponent_r17__Format : T_Format FrequencyComponent_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FrequencyComponent_r17__nat__Format FrequencyComponent_r17__F1 FrequencyComponent_r17__F2 FrequencyComponent_r17__F1F2 FrequencyComponent_r17__F2F1.

Opaque FrequencyComponent_r17__cond FrequencyComponent_r17__Format.

