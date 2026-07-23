Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive EstablishmentCause__Type : Set :=
 | EstablishmentCause__emergency
 | EstablishmentCause__highPriorityAccess
 | EstablishmentCause__mt_Access
 | EstablishmentCause__mo_Signalling
 | EstablishmentCause__mo_Data
 | EstablishmentCause__mo_VoiceCall
 | EstablishmentCause__mo_VideoCall
 | EstablishmentCause__mo_SMS
 | EstablishmentCause__mps_PriorityAccess
 | EstablishmentCause__mcs_PriorityAccess
 | EstablishmentCause__spare6
 | EstablishmentCause__spare5
 | EstablishmentCause__spare4
 | EstablishmentCause__spare3
 | EstablishmentCause__spare2
 | EstablishmentCause__spare1
.
Definition EstablishmentCause__cond := (fun (_ : EstablishmentCause__Type) => True).
Lemma EstablishmentCause__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EstablishmentCause__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 EstablishmentCause__nat__helper.

Definition EstablishmentCause__F1 t :=
  match t with
  | EstablishmentCause__emergency => 0
  | EstablishmentCause__highPriorityAccess => 1
  | EstablishmentCause__mt_Access => 2
  | EstablishmentCause__mo_Signalling => 3
  | EstablishmentCause__mo_Data => 4
  | EstablishmentCause__mo_VoiceCall => 5
  | EstablishmentCause__mo_VideoCall => 6
  | EstablishmentCause__mo_SMS => 7
  | EstablishmentCause__mps_PriorityAccess => 8
  | EstablishmentCause__mcs_PriorityAccess => 9
  | EstablishmentCause__spare6 => 10
  | EstablishmentCause__spare5 => 11
  | EstablishmentCause__spare4 => 12
  | EstablishmentCause__spare3 => 13
  | EstablishmentCause__spare2 => 14
  | EstablishmentCause__spare1 => 15
  end.
Definition EstablishmentCause__F2 n :=
  match n with
  | 0 => EstablishmentCause__emergency
  | 1 => EstablishmentCause__highPriorityAccess
  | 2 => EstablishmentCause__mt_Access
  | 3 => EstablishmentCause__mo_Signalling
  | 4 => EstablishmentCause__mo_Data
  | 5 => EstablishmentCause__mo_VoiceCall
  | 6 => EstablishmentCause__mo_VideoCall
  | 7 => EstablishmentCause__mo_SMS
  | 8 => EstablishmentCause__mps_PriorityAccess
  | 9 => EstablishmentCause__mcs_PriorityAccess
  | 10 => EstablishmentCause__spare6
  | 11 => EstablishmentCause__spare5
  | 12 => EstablishmentCause__spare4
  | 13 => EstablishmentCause__spare3
  | 14 => EstablishmentCause__spare2
  | 15 => EstablishmentCause__spare1
  | _ => EstablishmentCause__emergency
  end.
Lemma EstablishmentCause__F1F2 : forall x : EstablishmentCause__Type, (EstablishmentCause__F1 x <= 15) /\ EstablishmentCause__F2 (EstablishmentCause__F1 x) = x. imp_solve. Qed.
Lemma EstablishmentCause__F2F1 : forall (y : nat) (H : y <= 15), EstablishmentCause__F1 (EstablishmentCause__F2 y) = y. enum_solve H y. Qed.


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
Definition EstablishmentCause__Format : T_Format EstablishmentCause__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EstablishmentCause__nat__Format EstablishmentCause__F1 EstablishmentCause__F2 EstablishmentCause__F1F2 EstablishmentCause__F2F1.

Opaque EstablishmentCause__cond EstablishmentCause__Format.

