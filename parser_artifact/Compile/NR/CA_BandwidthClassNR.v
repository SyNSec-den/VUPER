Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CA_BandwidthClassNR__root__Type : Set :=
 | CA_BandwidthClassNR__root__a
 | CA_BandwidthClassNR__root__b
 | CA_BandwidthClassNR__root__c
 | CA_BandwidthClassNR__root__d
 | CA_BandwidthClassNR__root__e
 | CA_BandwidthClassNR__root__f
 | CA_BandwidthClassNR__root__g
 | CA_BandwidthClassNR__root__h
 | CA_BandwidthClassNR__root__i
 | CA_BandwidthClassNR__root__j
 | CA_BandwidthClassNR__root__k
 | CA_BandwidthClassNR__root__l
 | CA_BandwidthClassNR__root__m
 | CA_BandwidthClassNR__root__n
 | CA_BandwidthClassNR__root__o
 | CA_BandwidthClassNR__root__p
 | CA_BandwidthClassNR__root__q
.
Definition CA_BandwidthClassNR__root__cond := (fun (_ : CA_BandwidthClassNR__root__Type) => True).
Lemma CA_BandwidthClassNR__root__nat__helper : to_bit_sz 16 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_BandwidthClassNR__root__nat__Format : T_Format nat (fun z => (z <= 16)) :=
  nat_enum_format 16 CA_BandwidthClassNR__root__nat__helper.

Definition CA_BandwidthClassNR__root__F1 t :=
  match t with
  | CA_BandwidthClassNR__root__a => 0
  | CA_BandwidthClassNR__root__b => 1
  | CA_BandwidthClassNR__root__c => 2
  | CA_BandwidthClassNR__root__d => 3
  | CA_BandwidthClassNR__root__e => 4
  | CA_BandwidthClassNR__root__f => 5
  | CA_BandwidthClassNR__root__g => 6
  | CA_BandwidthClassNR__root__h => 7
  | CA_BandwidthClassNR__root__i => 8
  | CA_BandwidthClassNR__root__j => 9
  | CA_BandwidthClassNR__root__k => 10
  | CA_BandwidthClassNR__root__l => 11
  | CA_BandwidthClassNR__root__m => 12
  | CA_BandwidthClassNR__root__n => 13
  | CA_BandwidthClassNR__root__o => 14
  | CA_BandwidthClassNR__root__p => 15
  | CA_BandwidthClassNR__root__q => 16
  end.
Definition CA_BandwidthClassNR__root__F2 n :=
  match n with
  | 0 => CA_BandwidthClassNR__root__a
  | 1 => CA_BandwidthClassNR__root__b
  | 2 => CA_BandwidthClassNR__root__c
  | 3 => CA_BandwidthClassNR__root__d
  | 4 => CA_BandwidthClassNR__root__e
  | 5 => CA_BandwidthClassNR__root__f
  | 6 => CA_BandwidthClassNR__root__g
  | 7 => CA_BandwidthClassNR__root__h
  | 8 => CA_BandwidthClassNR__root__i
  | 9 => CA_BandwidthClassNR__root__j
  | 10 => CA_BandwidthClassNR__root__k
  | 11 => CA_BandwidthClassNR__root__l
  | 12 => CA_BandwidthClassNR__root__m
  | 13 => CA_BandwidthClassNR__root__n
  | 14 => CA_BandwidthClassNR__root__o
  | 15 => CA_BandwidthClassNR__root__p
  | 16 => CA_BandwidthClassNR__root__q
  | _ => CA_BandwidthClassNR__root__a
  end.
Lemma CA_BandwidthClassNR__root__F1F2 : forall x : CA_BandwidthClassNR__root__Type, (CA_BandwidthClassNR__root__F1 x <= 16) /\ CA_BandwidthClassNR__root__F2 (CA_BandwidthClassNR__root__F1 x) = x. imp_solve. Qed.
Lemma CA_BandwidthClassNR__root__F2F1 : forall (y : nat) (H : y <= 16), CA_BandwidthClassNR__root__F1 (CA_BandwidthClassNR__root__F2 y) = y. enum_solve H y. Qed.

Inductive CA_BandwidthClassNR__ext__Type : Set :=
 | CA_BandwidthClassNR__ext__r2_v1730
 | CA_BandwidthClassNR__ext__r3_v1730
 | CA_BandwidthClassNR__ext__r4_v1730
 | CA_BandwidthClassNR__ext__r5_v1730
 | CA_BandwidthClassNR__ext__r6_v1730
 | CA_BandwidthClassNR__ext__r7_v1730
 | CA_BandwidthClassNR__ext__r8_v1730
 | CA_BandwidthClassNR__ext__r9_v1730
 | CA_BandwidthClassNR__ext__r10_v1730
 | CA_BandwidthClassNR__ext__r11_v1730
 | CA_BandwidthClassNR__ext__r12_v1730
.
Definition CA_BandwidthClassNR__ext__cond := (fun (_ : CA_BandwidthClassNR__ext__Type) => True).
Lemma CA_BandwidthClassNR__ext__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_BandwidthClassNR__ext__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 CA_BandwidthClassNR__ext__nat__helper.

Definition CA_BandwidthClassNR__ext__F1 t :=
  match t with
  | CA_BandwidthClassNR__ext__r2_v1730 => 0
  | CA_BandwidthClassNR__ext__r3_v1730 => 1
  | CA_BandwidthClassNR__ext__r4_v1730 => 2
  | CA_BandwidthClassNR__ext__r5_v1730 => 3
  | CA_BandwidthClassNR__ext__r6_v1730 => 4
  | CA_BandwidthClassNR__ext__r7_v1730 => 5
  | CA_BandwidthClassNR__ext__r8_v1730 => 6
  | CA_BandwidthClassNR__ext__r9_v1730 => 7
  | CA_BandwidthClassNR__ext__r10_v1730 => 8
  | CA_BandwidthClassNR__ext__r11_v1730 => 9
  | CA_BandwidthClassNR__ext__r12_v1730 => 10
  end.
Definition CA_BandwidthClassNR__ext__F2 n :=
  match n with
  | 0 => CA_BandwidthClassNR__ext__r2_v1730
  | 1 => CA_BandwidthClassNR__ext__r3_v1730
  | 2 => CA_BandwidthClassNR__ext__r4_v1730
  | 3 => CA_BandwidthClassNR__ext__r5_v1730
  | 4 => CA_BandwidthClassNR__ext__r6_v1730
  | 5 => CA_BandwidthClassNR__ext__r7_v1730
  | 6 => CA_BandwidthClassNR__ext__r8_v1730
  | 7 => CA_BandwidthClassNR__ext__r9_v1730
  | 8 => CA_BandwidthClassNR__ext__r10_v1730
  | 9 => CA_BandwidthClassNR__ext__r11_v1730
  | 10 => CA_BandwidthClassNR__ext__r12_v1730
  | _ => CA_BandwidthClassNR__ext__r2_v1730
  end.
Lemma CA_BandwidthClassNR__ext__F1F2 : forall x : CA_BandwidthClassNR__ext__Type, (CA_BandwidthClassNR__ext__F1 x <= 10) /\ CA_BandwidthClassNR__ext__F2 (CA_BandwidthClassNR__ext__F1 x) = x. imp_solve. Qed.
Lemma CA_BandwidthClassNR__ext__F2F1 : forall (y : nat) (H : y <= 10), CA_BandwidthClassNR__ext__F1 (CA_BandwidthClassNR__ext__F2 y) = y. enum_solve H y. Qed.

Lemma CA_BandwidthClassNR__ext__helper1 : forall a, a <= 10 -> a <= 63. lia. Qed.
Definition CA_BandwidthClassNR__ext__helper_format : T_Format nat (fun n => n <= 10) :=
            restrict_format (fun n : nat => n <= 10)
                  small_integer_format
                  CA_BandwidthClassNR__ext__helper1
                  (fun a => Compare_dec.le_dec a 10).
Definition CA_BandwidthClassNR__Type : Set := CA_BandwidthClassNR__root__Type + CA_BandwidthClassNR__ext__Type.
Definition CA_BandwidthClassNR__cond := sum_cond CA_BandwidthClassNR__root__cond CA_BandwidthClassNR__ext__cond.


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
Definition CA_BandwidthClassNR__root__Format : T_Format CA_BandwidthClassNR__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format CA_BandwidthClassNR__root__nat__Format CA_BandwidthClassNR__root__F1 CA_BandwidthClassNR__root__F2 CA_BandwidthClassNR__root__F1F2 CA_BandwidthClassNR__root__F2F1.

Opaque CA_BandwidthClassNR__root__cond CA_BandwidthClassNR__root__Format.

Definition CA_BandwidthClassNR__ext__Format : T_Format CA_BandwidthClassNR__ext__Type CA_BandwidthClassNR__ext__cond :=
proj3_format CA_BandwidthClassNR__ext__helper_format CA_BandwidthClassNR__ext__F1 CA_BandwidthClassNR__ext__F2 CA_BandwidthClassNR__ext__F1F2 CA_BandwidthClassNR__ext__F2F1.

Opaque CA_BandwidthClassNR__ext__cond CA_BandwidthClassNR__ext__Format.

Definition CA_BandwidthClassNR__Format : T_Format CA_BandwidthClassNR__Type CA_BandwidthClassNR__cond := sum_format CA_BandwidthClassNR__root__Format CA_BandwidthClassNR__ext__Format.
Opaque CA_BandwidthClassNR__cond CA_BandwidthClassNR__Format.

Opaque CA_BandwidthClassNR__cond CA_BandwidthClassNR__Format.

