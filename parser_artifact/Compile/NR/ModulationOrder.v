Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ModulationOrder__Type : Set :=
 | ModulationOrder__bpsk_halfpi
 | ModulationOrder__bpsk
 | ModulationOrder__qpsk
 | ModulationOrder__qam16
 | ModulationOrder__qam64
 | ModulationOrder__qam256
.
Definition ModulationOrder__cond := (fun (_ : ModulationOrder__Type) => True).
Lemma ModulationOrder__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ModulationOrder__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 ModulationOrder__nat__helper.

Definition ModulationOrder__F1 t :=
  match t with
  | ModulationOrder__bpsk_halfpi => 0
  | ModulationOrder__bpsk => 1
  | ModulationOrder__qpsk => 2
  | ModulationOrder__qam16 => 3
  | ModulationOrder__qam64 => 4
  | ModulationOrder__qam256 => 5
  end.
Definition ModulationOrder__F2 n :=
  match n with
  | 0 => ModulationOrder__bpsk_halfpi
  | 1 => ModulationOrder__bpsk
  | 2 => ModulationOrder__qpsk
  | 3 => ModulationOrder__qam16
  | 4 => ModulationOrder__qam64
  | 5 => ModulationOrder__qam256
  | _ => ModulationOrder__bpsk_halfpi
  end.
Lemma ModulationOrder__F1F2 : forall x : ModulationOrder__Type, (ModulationOrder__F1 x <= 5) /\ ModulationOrder__F2 (ModulationOrder__F1 x) = x. imp_solve. Qed.
Lemma ModulationOrder__F2F1 : forall (y : nat) (H : y <= 5), ModulationOrder__F1 (ModulationOrder__F2 y) = y. enum_solve H y. Qed.


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
Definition ModulationOrder__Format : T_Format ModulationOrder__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ModulationOrder__nat__Format ModulationOrder__F1 ModulationOrder__F2 ModulationOrder__F1F2 ModulationOrder__F2F1.

Opaque ModulationOrder__cond ModulationOrder__Format.

