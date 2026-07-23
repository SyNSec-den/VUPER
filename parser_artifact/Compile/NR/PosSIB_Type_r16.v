Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PosSIB_Type_r16__encrypted_r16__Type : Set :=
 | PosSIB_Type_r16__encrypted_r16__true
.
Definition PosSIB_Type_r16__encrypted_r16__cond := (fun (_ : PosSIB_Type_r16__encrypted_r16__Type) => True).
Lemma PosSIB_Type_r16__encrypted_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosSIB_Type_r16__encrypted_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PosSIB_Type_r16__encrypted_r16__nat__helper.

Definition PosSIB_Type_r16__encrypted_r16__F1 t :=
  match t with
  | PosSIB_Type_r16__encrypted_r16__true => 0
  end.
Definition PosSIB_Type_r16__encrypted_r16__F2 n :=
  match n with
  | 0 => PosSIB_Type_r16__encrypted_r16__true
  | _ => PosSIB_Type_r16__encrypted_r16__true
  end.
Lemma PosSIB_Type_r16__encrypted_r16__F1F2 : forall x : PosSIB_Type_r16__encrypted_r16__Type, (PosSIB_Type_r16__encrypted_r16__F1 x <= 0) /\ PosSIB_Type_r16__encrypted_r16__F2 (PosSIB_Type_r16__encrypted_r16__F1 x) = x. imp_solve. Qed.
Lemma PosSIB_Type_r16__encrypted_r16__F2F1 : forall (y : nat) (H : y <= 0), PosSIB_Type_r16__encrypted_r16__F1 (PosSIB_Type_r16__encrypted_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.GNSS_ID_r16.

Opaque GNSS_ID_r16__cond GNSS_ID_r16__Format.

Require Import NR.SBAS_ID_r16.

Opaque SBAS_ID_r16__cond SBAS_ID_r16__Format.

Inductive PosSIB_Type_r16__posSibType_r16__root__Type : Set :=
 | PosSIB_Type_r16__posSibType_r16__root__posSibType1_1
 | PosSIB_Type_r16__posSibType_r16__root__posSibType1_2
 | PosSIB_Type_r16__posSibType_r16__root__posSibType1_3
 | PosSIB_Type_r16__posSibType_r16__root__posSibType1_4
 | PosSIB_Type_r16__posSibType_r16__root__posSibType1_5
 | PosSIB_Type_r16__posSibType_r16__root__posSibType1_6
 | PosSIB_Type_r16__posSibType_r16__root__posSibType1_7
 | PosSIB_Type_r16__posSibType_r16__root__posSibType1_8
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_1
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_2
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_3
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_4
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_5
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_6
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_7
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_8
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_9
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_10
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_11
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_12
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_13
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_14
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_15
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_16
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_17
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_18
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_19
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_20
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_21
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_22
 | PosSIB_Type_r16__posSibType_r16__root__posSibType2_23
 | PosSIB_Type_r16__posSibType_r16__root__posSibType3_1
 | PosSIB_Type_r16__posSibType_r16__root__posSibType4_1
 | PosSIB_Type_r16__posSibType_r16__root__posSibType5_1
 | PosSIB_Type_r16__posSibType_r16__root__posSibType6_1
 | PosSIB_Type_r16__posSibType_r16__root__posSibType6_2
 | PosSIB_Type_r16__posSibType_r16__root__posSibType6_3
.
Definition PosSIB_Type_r16__posSibType_r16__root__cond := (fun (_ : PosSIB_Type_r16__posSibType_r16__root__Type) => True).
Lemma PosSIB_Type_r16__posSibType_r16__root__nat__helper : to_bit_sz 36 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosSIB_Type_r16__posSibType_r16__root__nat__Format : T_Format nat (fun z => (z <= 36)) :=
  nat_enum_format 36 PosSIB_Type_r16__posSibType_r16__root__nat__helper.

Definition PosSIB_Type_r16__posSibType_r16__root__F1 t :=
  match t with
  | PosSIB_Type_r16__posSibType_r16__root__posSibType1_1 => 0
  | PosSIB_Type_r16__posSibType_r16__root__posSibType1_2 => 1
  | PosSIB_Type_r16__posSibType_r16__root__posSibType1_3 => 2
  | PosSIB_Type_r16__posSibType_r16__root__posSibType1_4 => 3
  | PosSIB_Type_r16__posSibType_r16__root__posSibType1_5 => 4
  | PosSIB_Type_r16__posSibType_r16__root__posSibType1_6 => 5
  | PosSIB_Type_r16__posSibType_r16__root__posSibType1_7 => 6
  | PosSIB_Type_r16__posSibType_r16__root__posSibType1_8 => 7
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_1 => 8
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_2 => 9
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_3 => 10
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_4 => 11
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_5 => 12
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_6 => 13
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_7 => 14
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_8 => 15
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_9 => 16
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_10 => 17
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_11 => 18
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_12 => 19
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_13 => 20
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_14 => 21
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_15 => 22
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_16 => 23
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_17 => 24
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_18 => 25
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_19 => 26
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_20 => 27
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_21 => 28
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_22 => 29
  | PosSIB_Type_r16__posSibType_r16__root__posSibType2_23 => 30
  | PosSIB_Type_r16__posSibType_r16__root__posSibType3_1 => 31
  | PosSIB_Type_r16__posSibType_r16__root__posSibType4_1 => 32
  | PosSIB_Type_r16__posSibType_r16__root__posSibType5_1 => 33
  | PosSIB_Type_r16__posSibType_r16__root__posSibType6_1 => 34
  | PosSIB_Type_r16__posSibType_r16__root__posSibType6_2 => 35
  | PosSIB_Type_r16__posSibType_r16__root__posSibType6_3 => 36
  end.
Definition PosSIB_Type_r16__posSibType_r16__root__F2 n :=
  match n with
  | 0 => PosSIB_Type_r16__posSibType_r16__root__posSibType1_1
  | 1 => PosSIB_Type_r16__posSibType_r16__root__posSibType1_2
  | 2 => PosSIB_Type_r16__posSibType_r16__root__posSibType1_3
  | 3 => PosSIB_Type_r16__posSibType_r16__root__posSibType1_4
  | 4 => PosSIB_Type_r16__posSibType_r16__root__posSibType1_5
  | 5 => PosSIB_Type_r16__posSibType_r16__root__posSibType1_6
  | 6 => PosSIB_Type_r16__posSibType_r16__root__posSibType1_7
  | 7 => PosSIB_Type_r16__posSibType_r16__root__posSibType1_8
  | 8 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_1
  | 9 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_2
  | 10 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_3
  | 11 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_4
  | 12 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_5
  | 13 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_6
  | 14 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_7
  | 15 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_8
  | 16 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_9
  | 17 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_10
  | 18 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_11
  | 19 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_12
  | 20 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_13
  | 21 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_14
  | 22 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_15
  | 23 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_16
  | 24 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_17
  | 25 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_18
  | 26 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_19
  | 27 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_20
  | 28 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_21
  | 29 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_22
  | 30 => PosSIB_Type_r16__posSibType_r16__root__posSibType2_23
  | 31 => PosSIB_Type_r16__posSibType_r16__root__posSibType3_1
  | 32 => PosSIB_Type_r16__posSibType_r16__root__posSibType4_1
  | 33 => PosSIB_Type_r16__posSibType_r16__root__posSibType5_1
  | 34 => PosSIB_Type_r16__posSibType_r16__root__posSibType6_1
  | 35 => PosSIB_Type_r16__posSibType_r16__root__posSibType6_2
  | 36 => PosSIB_Type_r16__posSibType_r16__root__posSibType6_3
  | _ => PosSIB_Type_r16__posSibType_r16__root__posSibType1_1
  end.
Lemma PosSIB_Type_r16__posSibType_r16__root__F1F2 : forall x : PosSIB_Type_r16__posSibType_r16__root__Type, (PosSIB_Type_r16__posSibType_r16__root__F1 x <= 36) /\ PosSIB_Type_r16__posSibType_r16__root__F2 (PosSIB_Type_r16__posSibType_r16__root__F1 x) = x. imp_solve. Qed.
Lemma PosSIB_Type_r16__posSibType_r16__root__F2F1 : forall (y : nat) (H : y <= 36), PosSIB_Type_r16__posSibType_r16__root__F1 (PosSIB_Type_r16__posSibType_r16__root__F2 y) = y. enum_solve H y. Qed.

Definition PosSIB_Type_r16__posSibType_r16__ext__Type : Set := Empty_set.
Definition PosSIB_Type_r16__posSibType_r16__ext__cond := (fun (_ : PosSIB_Type_r16__posSibType_r16__ext__Type) => True).
Definition PosSIB_Type_r16__posSibType_r16__Type : Set := PosSIB_Type_r16__posSibType_r16__root__Type + PosSIB_Type_r16__posSibType_r16__ext__Type.
Definition PosSIB_Type_r16__posSibType_r16__cond := sum_cond PosSIB_Type_r16__posSibType_r16__root__cond PosSIB_Type_r16__posSibType_r16__ext__cond.

Inductive PosSIB_Type_r16__areaScope_r16__Type : Set :=
 | PosSIB_Type_r16__areaScope_r16__true
.
Definition PosSIB_Type_r16__areaScope_r16__cond := (fun (_ : PosSIB_Type_r16__areaScope_r16__Type) => True).
Lemma PosSIB_Type_r16__areaScope_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PosSIB_Type_r16__areaScope_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PosSIB_Type_r16__areaScope_r16__nat__helper.

Definition PosSIB_Type_r16__areaScope_r16__F1 t :=
  match t with
  | PosSIB_Type_r16__areaScope_r16__true => 0
  end.
Definition PosSIB_Type_r16__areaScope_r16__F2 n :=
  match n with
  | 0 => PosSIB_Type_r16__areaScope_r16__true
  | _ => PosSIB_Type_r16__areaScope_r16__true
  end.
Lemma PosSIB_Type_r16__areaScope_r16__F1F2 : forall x : PosSIB_Type_r16__areaScope_r16__Type, (PosSIB_Type_r16__areaScope_r16__F1 x <= 0) /\ PosSIB_Type_r16__areaScope_r16__F2 (PosSIB_Type_r16__areaScope_r16__F1 x) = x. imp_solve. Qed.
Lemma PosSIB_Type_r16__areaScope_r16__F2F1 : forall (y : nat) (H : y <= 0), PosSIB_Type_r16__areaScope_r16__F1 (PosSIB_Type_r16__areaScope_r16__F2 y) = y. enum_solve H y. Qed.

Record PosSIB_Type_r16__Type : Set :=
  make__PosSIB_Type_r16__Type {
    PosSIB_Type_r16__encrypted_r16 : option PosSIB_Type_r16__encrypted_r16__Type ;
    PosSIB_Type_r16__gnss_id_r16 : option GNSS_ID_r16__Type ;
    PosSIB_Type_r16__sbas_id_r16 : option SBAS_ID_r16__Type ;
    PosSIB_Type_r16__posSibType_r16 : PosSIB_Type_r16__posSibType_r16__Type ;
    PosSIB_Type_r16__areaScope_r16 : option PosSIB_Type_r16__areaScope_r16__Type ;
}.
Definition PosSIB_Type_r16__list := (
 Opt PosSIB_Type_r16__encrypted_r16__Type PosSIB_Type_r16__encrypted_r16__cond ::
 Opt GNSS_ID_r16__Type GNSS_ID_r16__cond ::
 Opt SBAS_ID_r16__Type SBAS_ID_r16__cond ::
 Nor PosSIB_Type_r16__posSibType_r16__Type PosSIB_Type_r16__posSibType_r16__cond ::
 Opt PosSIB_Type_r16__areaScope_r16__Type PosSIB_Type_r16__areaScope_r16__cond ::
 nil).
Definition PosSIB_Type_r16__cond z := 
  opt_cond PosSIB_Type_r16__encrypted_r16__cond (PosSIB_Type_r16__encrypted_r16 z) /\
  opt_cond GNSS_ID_r16__cond (PosSIB_Type_r16__gnss_id_r16 z) /\
  opt_cond SBAS_ID_r16__cond (PosSIB_Type_r16__sbas_id_r16 z) /\
  PosSIB_Type_r16__posSibType_r16__cond (PosSIB_Type_r16__posSibType_r16 z) /\
  opt_cond PosSIB_Type_r16__areaScope_r16__cond (PosSIB_Type_r16__areaScope_r16 z) /\
  True.


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
Definition PosSIB_Type_r16__encrypted_r16__Format : T_Format PosSIB_Type_r16__encrypted_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosSIB_Type_r16__encrypted_r16__nat__Format PosSIB_Type_r16__encrypted_r16__F1 PosSIB_Type_r16__encrypted_r16__F2 PosSIB_Type_r16__encrypted_r16__F1F2 PosSIB_Type_r16__encrypted_r16__F2F1.

Opaque PosSIB_Type_r16__encrypted_r16__cond PosSIB_Type_r16__encrypted_r16__Format.

Definition PosSIB_Type_r16__posSibType_r16__root__Format : T_Format PosSIB_Type_r16__posSibType_r16__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format PosSIB_Type_r16__posSibType_r16__root__nat__Format PosSIB_Type_r16__posSibType_r16__root__F1 PosSIB_Type_r16__posSibType_r16__root__F2 PosSIB_Type_r16__posSibType_r16__root__F1F2 PosSIB_Type_r16__posSibType_r16__root__F2F1.

Opaque PosSIB_Type_r16__posSibType_r16__root__cond PosSIB_Type_r16__posSibType_r16__root__Format.

Definition PosSIB_Type_r16__posSibType_r16__ext__Format : T_Format PosSIB_Type_r16__posSibType_r16__ext__Type PosSIB_Type_r16__posSibType_r16__ext__cond := empty_format.

Opaque PosSIB_Type_r16__posSibType_r16__ext__cond PosSIB_Type_r16__posSibType_r16__ext__Format.

Definition PosSIB_Type_r16__posSibType_r16__Format : T_Format PosSIB_Type_r16__posSibType_r16__Type PosSIB_Type_r16__posSibType_r16__cond := sum_format PosSIB_Type_r16__posSibType_r16__root__Format PosSIB_Type_r16__posSibType_r16__ext__Format.
Opaque PosSIB_Type_r16__posSibType_r16__cond PosSIB_Type_r16__posSibType_r16__Format.

Opaque PosSIB_Type_r16__posSibType_r16__cond PosSIB_Type_r16__posSibType_r16__Format.

Definition PosSIB_Type_r16__areaScope_r16__Format : T_Format PosSIB_Type_r16__areaScope_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PosSIB_Type_r16__areaScope_r16__nat__Format PosSIB_Type_r16__areaScope_r16__F1 PosSIB_Type_r16__areaScope_r16__F2 PosSIB_Type_r16__areaScope_r16__F1F2 PosSIB_Type_r16__areaScope_r16__F2F1.

Opaque PosSIB_Type_r16__areaScope_r16__cond PosSIB_Type_r16__areaScope_r16__Format.


Definition PosSIB_Type_r16__Format_Type := Eval cbn in seq_format_prod PosSIB_Type_r16__list.
Definition PosSIB_Type_r16__Format_list : PosSIB_Type_r16__Format_Type :=
  (PosSIB_Type_r16__encrypted_r16__Format, (GNSS_ID_r16__Format, (SBAS_ID_r16__Format, (PosSIB_Type_r16__posSibType_r16__Format, (PosSIB_Type_r16__areaScope_r16__Format, unit_format))))).
Definition PosSIB_Type_r16__list__Format := (*Eval compute in *) seq_format PosSIB_Type_r16__list PosSIB_Type_r16__Format_list.
Definition PosSIB_Type_r16__F1 z :=
  (PosSIB_Type_r16__encrypted_r16 z, (PosSIB_Type_r16__gnss_id_r16 z, (PosSIB_Type_r16__sbas_id_r16 z, (PosSIB_Type_r16__posSibType_r16 z, (PosSIB_Type_r16__areaScope_r16 z, tt))))).
Definition PosSIB_Type_r16__F2 (y : seq_type PosSIB_Type_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__PosSIB_Type_r16__Type i0 i1 i2 i3 i4
  end.
Lemma PosSIB_Type_r16__F1F2_cond (z : PosSIB_Type_r16__Type)
  : PosSIB_Type_r16__cond z ->
  (seq_cond PosSIB_Type_r16__list (PosSIB_Type_r16__F1 z)).
intro H. unfold PosSIB_Type_r16__cond in H. simpl. auto. Qed.
Lemma PosSIB_Type_r16__F1F2_cond2 (z : PosSIB_Type_r16__Type)
 : PosSIB_Type_r16__F2 (PosSIB_Type_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PosSIB_Type_r16__F2F1_cond (y : seq_type PosSIB_Type_r16__list)
  : seq_cond PosSIB_Type_r16__list y ->
 (PosSIB_Type_r16__cond (PosSIB_Type_r16__F2 y)) /\  PosSIB_Type_r16__F1 (PosSIB_Type_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PosSIB_Type_r16__cond. simpl in *. auto.
 - simpl. unfold PosSIB_Type_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PosSIB_Type_r16__Format : T_Format PosSIB_Type_r16__Type PosSIB_Type_r16__cond :=
        proj2_format  PosSIB_Type_r16__cond PosSIB_Type_r16__list__Format
    PosSIB_Type_r16__F1 PosSIB_Type_r16__F2 PosSIB_Type_r16__F1F2_cond  PosSIB_Type_r16__F1F2_cond2 PosSIB_Type_r16__F2F1_cond.
Opaque PosSIB_Type_r16__cond PosSIB_Type_r16__Format.

