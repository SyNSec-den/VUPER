Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ResumeCause__Type : Set :=
 | ResumeCause__emergency
 | ResumeCause__highPriorityAccess
 | ResumeCause__mt_Access
 | ResumeCause__mo_Signalling
 | ResumeCause__mo_Data
 | ResumeCause__mo_VoiceCall
 | ResumeCause__mo_VideoCall
 | ResumeCause__mo_SMS
 | ResumeCause__rna_Update
 | ResumeCause__mps_PriorityAccess
 | ResumeCause__mcs_PriorityAccess
 | ResumeCause__spare1
 | ResumeCause__spare2
 | ResumeCause__spare3
 | ResumeCause__spare4
 | ResumeCause__spare5
.
Definition ResumeCause__cond := (fun (_ : ResumeCause__Type) => True).
Lemma ResumeCause__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ResumeCause__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 ResumeCause__nat__helper.

Definition ResumeCause__F1 t :=
  match t with
  | ResumeCause__emergency => 0
  | ResumeCause__highPriorityAccess => 1
  | ResumeCause__mt_Access => 2
  | ResumeCause__mo_Signalling => 3
  | ResumeCause__mo_Data => 4
  | ResumeCause__mo_VoiceCall => 5
  | ResumeCause__mo_VideoCall => 6
  | ResumeCause__mo_SMS => 7
  | ResumeCause__rna_Update => 8
  | ResumeCause__mps_PriorityAccess => 9
  | ResumeCause__mcs_PriorityAccess => 10
  | ResumeCause__spare1 => 11
  | ResumeCause__spare2 => 12
  | ResumeCause__spare3 => 13
  | ResumeCause__spare4 => 14
  | ResumeCause__spare5 => 15
  end.
Definition ResumeCause__F2 n :=
  match n with
  | 0 => ResumeCause__emergency
  | 1 => ResumeCause__highPriorityAccess
  | 2 => ResumeCause__mt_Access
  | 3 => ResumeCause__mo_Signalling
  | 4 => ResumeCause__mo_Data
  | 5 => ResumeCause__mo_VoiceCall
  | 6 => ResumeCause__mo_VideoCall
  | 7 => ResumeCause__mo_SMS
  | 8 => ResumeCause__rna_Update
  | 9 => ResumeCause__mps_PriorityAccess
  | 10 => ResumeCause__mcs_PriorityAccess
  | 11 => ResumeCause__spare1
  | 12 => ResumeCause__spare2
  | 13 => ResumeCause__spare3
  | 14 => ResumeCause__spare4
  | 15 => ResumeCause__spare5
  | _ => ResumeCause__emergency
  end.
Lemma ResumeCause__F1F2 : forall x : ResumeCause__Type, (ResumeCause__F1 x <= 15) /\ ResumeCause__F2 (ResumeCause__F1 x) = x. imp_solve. Qed.
Lemma ResumeCause__F2F1 : forall (y : nat) (H : y <= 15), ResumeCause__F1 (ResumeCause__F2 y) = y. enum_solve H y. Qed.


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
Definition ResumeCause__Format : T_Format ResumeCause__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ResumeCause__nat__Format ResumeCause__F1 ResumeCause__F2 ResumeCause__F1F2 ResumeCause__F2F1.

Opaque ResumeCause__cond ResumeCause__Format.

