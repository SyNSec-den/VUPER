Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CA_BandwidthClassEUTRA__root__Type : Set :=
 | CA_BandwidthClassEUTRA__root__a
 | CA_BandwidthClassEUTRA__root__b
 | CA_BandwidthClassEUTRA__root__c
 | CA_BandwidthClassEUTRA__root__d
 | CA_BandwidthClassEUTRA__root__e
 | CA_BandwidthClassEUTRA__root__f
.
Definition CA_BandwidthClassEUTRA__root__cond := (fun (_ : CA_BandwidthClassEUTRA__root__Type) => True).
Lemma CA_BandwidthClassEUTRA__root__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_BandwidthClassEUTRA__root__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 CA_BandwidthClassEUTRA__root__nat__helper.

Definition CA_BandwidthClassEUTRA__root__F1 t :=
  match t with
  | CA_BandwidthClassEUTRA__root__a => 0
  | CA_BandwidthClassEUTRA__root__b => 1
  | CA_BandwidthClassEUTRA__root__c => 2
  | CA_BandwidthClassEUTRA__root__d => 3
  | CA_BandwidthClassEUTRA__root__e => 4
  | CA_BandwidthClassEUTRA__root__f => 5
  end.
Definition CA_BandwidthClassEUTRA__root__F2 n :=
  match n with
  | 0 => CA_BandwidthClassEUTRA__root__a
  | 1 => CA_BandwidthClassEUTRA__root__b
  | 2 => CA_BandwidthClassEUTRA__root__c
  | 3 => CA_BandwidthClassEUTRA__root__d
  | 4 => CA_BandwidthClassEUTRA__root__e
  | 5 => CA_BandwidthClassEUTRA__root__f
  | _ => CA_BandwidthClassEUTRA__root__a
  end.
Lemma CA_BandwidthClassEUTRA__root__F1F2 : forall x : CA_BandwidthClassEUTRA__root__Type, (CA_BandwidthClassEUTRA__root__F1 x <= 5) /\ CA_BandwidthClassEUTRA__root__F2 (CA_BandwidthClassEUTRA__root__F1 x) = x. imp_solve. Qed.
Lemma CA_BandwidthClassEUTRA__root__F2F1 : forall (y : nat) (H : y <= 5), CA_BandwidthClassEUTRA__root__F1 (CA_BandwidthClassEUTRA__root__F2 y) = y. enum_solve H y. Qed.

Definition CA_BandwidthClassEUTRA__ext__Type : Set := Empty_set.
Definition CA_BandwidthClassEUTRA__ext__cond := (fun (_ : CA_BandwidthClassEUTRA__ext__Type) => True).
Definition CA_BandwidthClassEUTRA__Type : Set := CA_BandwidthClassEUTRA__root__Type + CA_BandwidthClassEUTRA__ext__Type.
Definition CA_BandwidthClassEUTRA__cond := sum_cond CA_BandwidthClassEUTRA__root__cond CA_BandwidthClassEUTRA__ext__cond.


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
Definition CA_BandwidthClassEUTRA__root__Format : T_Format CA_BandwidthClassEUTRA__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format CA_BandwidthClassEUTRA__root__nat__Format CA_BandwidthClassEUTRA__root__F1 CA_BandwidthClassEUTRA__root__F2 CA_BandwidthClassEUTRA__root__F1F2 CA_BandwidthClassEUTRA__root__F2F1.

Opaque CA_BandwidthClassEUTRA__root__cond CA_BandwidthClassEUTRA__root__Format.

Definition CA_BandwidthClassEUTRA__ext__Format : T_Format CA_BandwidthClassEUTRA__ext__Type CA_BandwidthClassEUTRA__ext__cond := empty_format.

Opaque CA_BandwidthClassEUTRA__ext__cond CA_BandwidthClassEUTRA__ext__Format.

Definition CA_BandwidthClassEUTRA__Format : T_Format CA_BandwidthClassEUTRA__Type CA_BandwidthClassEUTRA__cond := sum_format CA_BandwidthClassEUTRA__root__Format CA_BandwidthClassEUTRA__ext__Format.
Opaque CA_BandwidthClassEUTRA__cond CA_BandwidthClassEUTRA__Format.

Opaque CA_BandwidthClassEUTRA__cond CA_BandwidthClassEUTRA__Format.

