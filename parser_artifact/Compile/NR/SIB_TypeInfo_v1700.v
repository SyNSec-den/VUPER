Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__Type : Set :=
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType15
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType16
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType17
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType18
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType19
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType20
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType21
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare9
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare8
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare7
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare6
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare5
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare4
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare3
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare2
 | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare1
.
Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__cond := (fun (_ : SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__Type) => True).
Lemma SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__nat__helper.

Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F1 t :=
  match t with
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType15 => 0
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType16 => 1
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType17 => 2
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType18 => 3
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType19 => 4
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType20 => 5
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType21 => 6
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare9 => 7
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare8 => 8
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare7 => 9
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare6 => 10
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare5 => 11
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare4 => 12
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare3 => 13
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare2 => 14
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare1 => 15
  end.
Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F2 n :=
  match n with
  | 0 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType15
  | 1 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType16
  | 2 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType17
  | 3 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType18
  | 4 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType19
  | 5 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType20
  | 6 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType21
  | 7 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare9
  | 8 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare8
  | 9 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare7
  | 10 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare6
  | 11 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare5
  | 12 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare4
  | 13 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare3
  | 14 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare2
  | 15 => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__spare1
  | _ => SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__sibType15
  end.
Lemma SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F1F2 : forall x : SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__Type, (SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F1 x <= 15) /\ SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F2 (SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F1 x) = x. imp_solve. Qed.
Lemma SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F2F1 : forall (y : nat) (H : y <= 15), SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F1 (SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F2 y) = y. enum_solve H y. Qed.

Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__Type : Set := Empty_set.
Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__cond := (fun (_ : SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__Type) => True).
Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__Type : Set := SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__Type + SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__Type.
Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__cond := sum_cond SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__cond SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__cond.

Inductive SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__Type : Set :=
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType1_9
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType1_10
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType2_24
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType2_25
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_4
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_5
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_6
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare9
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare8
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare7
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare6
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare5
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare4
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare3
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare2
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare1
.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__cond := (fun (_ : SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__Type) => True).
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__nat__helper.

Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F1 t :=
  match t with
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType1_9 => 0
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType1_10 => 1
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType2_24 => 2
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType2_25 => 3
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_4 => 4
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_5 => 5
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_6 => 6
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare9 => 7
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare8 => 8
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare7 => 9
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare6 => 10
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare5 => 11
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare4 => 12
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare3 => 13
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare2 => 14
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare1 => 15
  end.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F2 n :=
  match n with
  | 0 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType1_9
  | 1 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType1_10
  | 2 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType2_24
  | 3 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType2_25
  | 4 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_4
  | 5 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_5
  | 6 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType6_6
  | 7 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare9
  | 8 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare8
  | 9 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare7
  | 10 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare6
  | 11 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare5
  | 12 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare4
  | 13 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare3
  | 14 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare2
  | 15 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__spare1
  | _ => SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__posSibType1_9
  end.
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F1F2 : forall x : SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__Type, (SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F1 x <= 15) /\ SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F2 (SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F1 x) = x. imp_solve. Qed.
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F2F1 : forall (y : nat) (H : y <= 15), SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F1 (SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F2 y) = y. enum_solve H y. Qed.

Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__Type : Set := Empty_set.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__cond := (fun (_ : SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__Type) => True).
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__Type : Set := SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__Type + SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__Type.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__cond := sum_cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__cond.

Inductive SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Type : Set :=
 | SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__true
.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__cond := (fun (_ : SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Type) => True).
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__nat__helper.

Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F1 t :=
  match t with
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__true => 0
  end.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F2 n :=
  match n with
  | 0 => SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__true
  | _ => SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__true
  end.
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F1F2 : forall x : SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Type, (SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F1 x <= 0) /\ SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F2 (SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F1 (SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.GNSS_ID_r16.

Opaque GNSS_ID_r16__cond GNSS_ID_r16__Format.

Require Import NR.SBAS_ID_r16.

Opaque SBAS_ID_r16__cond SBAS_ID_r16__Format.

Record SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type : Set :=
  make__SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type {
    SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17 : SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__Type ;
    SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17 : option SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Type ;
    SIB_TypeInfo_v1700__sibType_r17__type2_r17__gnss_id_r17 : option GNSS_ID_r16__Type ;
    SIB_TypeInfo_v1700__sibType_r17__type2_r17__sbas_id_r17 : option SBAS_ID_r16__Type ;
}.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__list := (
 Nor SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__Type SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__cond ::
 Opt SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Type SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__cond ::
 Opt GNSS_ID_r16__Type GNSS_ID_r16__cond ::
 Opt SBAS_ID_r16__Type SBAS_ID_r16__cond ::
 nil).
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond z := 
  SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__cond (SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17 z) /\
  opt_cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__cond (SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17 z) /\
  opt_cond GNSS_ID_r16__cond (SIB_TypeInfo_v1700__sibType_r17__type2_r17__gnss_id_r17 z) /\
  opt_cond SBAS_ID_r16__cond (SIB_TypeInfo_v1700__sibType_r17__type2_r17__sbas_id_r17 z) /\
  True.


Inductive SIB_TypeInfo_v1700__sibType_r17__Type : Set :=
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17 : SIB_TypeInfo_v1700__sibType_r17__type1_r17__Type -> SIB_TypeInfo_v1700__sibType_r17__Type
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17 : SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type -> SIB_TypeInfo_v1700__sibType_r17__Type
.
Definition SIB_TypeInfo_v1700__sibType_r17__list : list typ := (
typ_cons SIB_TypeInfo_v1700__sibType_r17__type1_r17__Type SIB_TypeInfo_v1700__sibType_r17__type1_r17__cond ::
typ_cons SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond ::
 nil).
Definition SIB_TypeInfo_v1700__sibType_r17__cond (c : SIB_TypeInfo_v1700__sibType_r17__Type) := 
  match c with
  | SIB_TypeInfo_v1700__sibType_r17__type1_r17 t => SIB_TypeInfo_v1700__sibType_r17__type1_r17__cond t 
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17 t => SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond t 
  end.

Lemma SIB_TypeInfo_v1700__sibType_r17__len_helper1 : to_bit_sz (length SIB_TypeInfo_v1700__sibType_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SIB_TypeInfo_v1700__sibType_r17__len_helper2 : 2 <= length2 SIB_TypeInfo_v1700__sibType_r17__list.
 simpl. lia. Qed.
Lemma SIB_TypeInfo_v1700__valueTag_r17__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma SIB_TypeInfo_v1700__valueTag_r17__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SIB_TypeInfo_v1700__valueTag_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB_TypeInfo_v1700__valueTag_r17__Type := Z.
Definition SIB_TypeInfo_v1700__valueTag_r17__cond := (fun z => (0 <= z <= 31)%Z).
Inductive SIB_TypeInfo_v1700__areaScope_r17__Type : Set :=
 | SIB_TypeInfo_v1700__areaScope_r17__true
.
Definition SIB_TypeInfo_v1700__areaScope_r17__cond := (fun (_ : SIB_TypeInfo_v1700__areaScope_r17__Type) => True).
Lemma SIB_TypeInfo_v1700__areaScope_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB_TypeInfo_v1700__areaScope_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB_TypeInfo_v1700__areaScope_r17__nat__helper.

Definition SIB_TypeInfo_v1700__areaScope_r17__F1 t :=
  match t with
  | SIB_TypeInfo_v1700__areaScope_r17__true => 0
  end.
Definition SIB_TypeInfo_v1700__areaScope_r17__F2 n :=
  match n with
  | 0 => SIB_TypeInfo_v1700__areaScope_r17__true
  | _ => SIB_TypeInfo_v1700__areaScope_r17__true
  end.
Lemma SIB_TypeInfo_v1700__areaScope_r17__F1F2 : forall x : SIB_TypeInfo_v1700__areaScope_r17__Type, (SIB_TypeInfo_v1700__areaScope_r17__F1 x <= 0) /\ SIB_TypeInfo_v1700__areaScope_r17__F2 (SIB_TypeInfo_v1700__areaScope_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB_TypeInfo_v1700__areaScope_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB_TypeInfo_v1700__areaScope_r17__F1 (SIB_TypeInfo_v1700__areaScope_r17__F2 y) = y. enum_solve H y. Qed.

Record SIB_TypeInfo_v1700__Type : Set :=
  make__SIB_TypeInfo_v1700__Type {
    SIB_TypeInfo_v1700__sibType_r17 : SIB_TypeInfo_v1700__sibType_r17__Type ;
    SIB_TypeInfo_v1700__valueTag_r17 : option Z ;
    SIB_TypeInfo_v1700__areaScope_r17 : option SIB_TypeInfo_v1700__areaScope_r17__Type ;
}.
Definition SIB_TypeInfo_v1700__list := (
 Nor SIB_TypeInfo_v1700__sibType_r17__Type SIB_TypeInfo_v1700__sibType_r17__cond ::
 Opt Z SIB_TypeInfo_v1700__valueTag_r17__cond ::
 Opt SIB_TypeInfo_v1700__areaScope_r17__Type SIB_TypeInfo_v1700__areaScope_r17__cond ::
 nil).
Definition SIB_TypeInfo_v1700__cond z := 
  SIB_TypeInfo_v1700__sibType_r17__cond (SIB_TypeInfo_v1700__sibType_r17 z) /\
  opt_cond SIB_TypeInfo_v1700__valueTag_r17__cond (SIB_TypeInfo_v1700__valueTag_r17 z) /\
  opt_cond SIB_TypeInfo_v1700__areaScope_r17__cond (SIB_TypeInfo_v1700__areaScope_r17 z) /\
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
Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__nat__Format SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F1 SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F2 SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F1F2 SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__F2F1.

Opaque SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__cond SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__Format.

Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__Type SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__cond := empty_format.

Opaque SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__cond SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__Format.

Definition SIB_TypeInfo_v1700__sibType_r17__type1_r17__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__type1_r17__Type SIB_TypeInfo_v1700__sibType_r17__type1_r17__cond := sum_format SIB_TypeInfo_v1700__sibType_r17__type1_r17__root__Format SIB_TypeInfo_v1700__sibType_r17__type1_r17__ext__Format.
Opaque SIB_TypeInfo_v1700__sibType_r17__type1_r17__cond SIB_TypeInfo_v1700__sibType_r17__type1_r17__Format.

Opaque SIB_TypeInfo_v1700__sibType_r17__type1_r17__cond SIB_TypeInfo_v1700__sibType_r17__type1_r17__Format.

Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__nat__Format SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F1 SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F2 SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F1F2 SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__F2F1.

Opaque SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__Format.

Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__Type SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__cond := empty_format.

Opaque SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__Format.

Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__Type SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__cond := sum_format SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__root__Format SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__ext__Format.
Opaque SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__Format.

Opaque SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__Format.

Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__nat__Format SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F1 SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F2 SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F1F2 SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__F2F1.

Opaque SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Format.


Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__Format_Type := Eval cbn in seq_format_prod SIB_TypeInfo_v1700__sibType_r17__type2_r17__list.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__Format_list : SIB_TypeInfo_v1700__sibType_r17__type2_r17__Format_Type :=
  (SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17__Format, (SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17__Format, (GNSS_ID_r16__Format, (SBAS_ID_r16__Format, unit_format)))).
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__list__Format := (*Eval compute in *) seq_format SIB_TypeInfo_v1700__sibType_r17__type2_r17__list SIB_TypeInfo_v1700__sibType_r17__type2_r17__Format_list.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1 z :=
  (SIB_TypeInfo_v1700__sibType_r17__type2_r17__posSibType_r17 z, (SIB_TypeInfo_v1700__sibType_r17__type2_r17__encrypted_r17 z, (SIB_TypeInfo_v1700__sibType_r17__type2_r17__gnss_id_r17 z, (SIB_TypeInfo_v1700__sibType_r17__type2_r17__sbas_id_r17 z, tt)))).
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__F2 (y : seq_type SIB_TypeInfo_v1700__sibType_r17__type2_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type i0 i1 i2 i3
  end.
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1F2_cond (z : SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type)
  : SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond z ->
  (seq_cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__list (SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1 z)).
intro H. unfold SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond in H. simpl. auto. Qed.
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1F2_cond2 (z : SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type)
 : SIB_TypeInfo_v1700__sibType_r17__type2_r17__F2 (SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB_TypeInfo_v1700__sibType_r17__type2_r17__F2F1_cond (y : seq_type SIB_TypeInfo_v1700__sibType_r17__type2_r17__list)
  : seq_cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__list y ->
 (SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond (SIB_TypeInfo_v1700__sibType_r17__type2_r17__F2 y)) /\  SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1 (SIB_TypeInfo_v1700__sibType_r17__type2_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond. simpl in *. auto.
 - simpl. unfold SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB_TypeInfo_v1700__sibType_r17__type2_r17__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond :=
        proj2_format  SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__list__Format
    SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1 SIB_TypeInfo_v1700__sibType_r17__type2_r17__F2 SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1F2_cond  SIB_TypeInfo_v1700__sibType_r17__type2_r17__F1F2_cond2 SIB_TypeInfo_v1700__sibType_r17__type2_r17__F2F1_cond.
Opaque SIB_TypeInfo_v1700__sibType_r17__type2_r17__cond SIB_TypeInfo_v1700__sibType_r17__type2_r17__Format.


Definition SIB_TypeInfo_v1700__sibType_r17__Format_Type := Eval cbn in get_formats SIB_TypeInfo_v1700__sibType_r17__list.
Definition SIB_TypeInfo_v1700__sibType_r17__Format_list : SIB_TypeInfo_v1700__sibType_r17__Format_Type :=
  (SIB_TypeInfo_v1700__sibType_r17__type1_r17__Format, (SIB_TypeInfo_v1700__sibType_r17__type2_r17__Format, unit__Format)).
Definition SIB_TypeInfo_v1700__sibType_r17__list__Format := Eval compute in choice_format SIB_TypeInfo_v1700__sibType_r17__list SIB_TypeInfo_v1700__sibType_r17__len_helper1 SIB_TypeInfo_v1700__sibType_r17__len_helper2  SIB_TypeInfo_v1700__sibType_r17__Format_list.
Definition SIB_TypeInfo_v1700__sibType_r17__F1 (z : SIB_TypeInfo_v1700__sibType_r17__Type) : (choice SIB_TypeInfo_v1700__sibType_r17__list) :=
  match z with
   | SIB_TypeInfo_v1700__sibType_r17__type1_r17 t => existT _ 0 t
  | SIB_TypeInfo_v1700__sibType_r17__type2_r17 t => existT _ 1 t
  end.
Definition SIB_TypeInfo_v1700__sibType_r17__g := (fun n => typ_set (get_nth_typ SIB_TypeInfo_v1700__sibType_r17__list n)).
Definition SIB_TypeInfo_v1700__sibType_r17__F2 (y : choice SIB_TypeInfo_v1700__sibType_r17__list) : SIB_TypeInfo_v1700__sibType_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SIB_TypeInfo_v1700__sibType_r17__g n -> SIB_TypeInfo_v1700__sibType_r17__Type) with
    | 0 => fun (t : SIB_TypeInfo_v1700__sibType_r17__type1_r17__Type) => SIB_TypeInfo_v1700__sibType_r17__type1_r17 t 
    | 1 => fun (t : SIB_TypeInfo_v1700__sibType_r17__type2_r17__Type) => SIB_TypeInfo_v1700__sibType_r17__type2_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SIB_TypeInfo_v1700__sibType_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SIB_TypeInfo_v1700__sibType_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SIB_TypeInfo_v1700__sibType_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SIB_TypeInfo_v1700__sibType_r17__Type with end) n0
           end t0).

Lemma SIB_TypeInfo_v1700__sibType_r17__helper2 :  forall (y : SIB_TypeInfo_v1700__sibType_r17__Type), SIB_TypeInfo_v1700__sibType_r17__cond y -> choice_cond SIB_TypeInfo_v1700__sibType_r17__list (SIB_TypeInfo_v1700__sibType_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SIB_TypeInfo_v1700__sibType_r17__helper3 :  forall (y : SIB_TypeInfo_v1700__sibType_r17__Type), SIB_TypeInfo_v1700__sibType_r17__F2 (SIB_TypeInfo_v1700__sibType_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SIB_TypeInfo_v1700__sibType_r17__helper4 : (forall b : choice SIB_TypeInfo_v1700__sibType_r17__list, choice_cond SIB_TypeInfo_v1700__sibType_r17__list b -> SIB_TypeInfo_v1700__sibType_r17__cond (SIB_TypeInfo_v1700__sibType_r17__F2 b) /\ SIB_TypeInfo_v1700__sibType_r17__F1 (SIB_TypeInfo_v1700__sibType_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SIB_TypeInfo_v1700__sibType_r17__F1 SIB_TypeInfo_v1700__sibType_r17__F2.
Definition SIB_TypeInfo_v1700__sibType_r17__Format : T_Format SIB_TypeInfo_v1700__sibType_r17__Type SIB_TypeInfo_v1700__sibType_r17__cond :=
  (* Eval compute in *) proj2_format SIB_TypeInfo_v1700__sibType_r17__cond SIB_TypeInfo_v1700__sibType_r17__list__Format SIB_TypeInfo_v1700__sibType_r17__F1 SIB_TypeInfo_v1700__sibType_r17__F2 SIB_TypeInfo_v1700__sibType_r17__helper2 SIB_TypeInfo_v1700__sibType_r17__helper3 SIB_TypeInfo_v1700__sibType_r17__helper4.
Opaque SIB_TypeInfo_v1700__sibType_r17__cond SIB_TypeInfo_v1700__sibType_r17__Format.

Definition SIB_TypeInfo_v1700__valueTag_r17__Format : T_Format Z SIB_TypeInfo_v1700__valueTag_r17__cond :=
 ranged_int_format (0) (31) SIB_TypeInfo_v1700__valueTag_r17__helper1 SIB_TypeInfo_v1700__valueTag_r17__helper2.

Opaque SIB_TypeInfo_v1700__valueTag_r17__cond SIB_TypeInfo_v1700__valueTag_r17__Format.

Definition SIB_TypeInfo_v1700__areaScope_r17__Format : T_Format SIB_TypeInfo_v1700__areaScope_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB_TypeInfo_v1700__areaScope_r17__nat__Format SIB_TypeInfo_v1700__areaScope_r17__F1 SIB_TypeInfo_v1700__areaScope_r17__F2 SIB_TypeInfo_v1700__areaScope_r17__F1F2 SIB_TypeInfo_v1700__areaScope_r17__F2F1.

Opaque SIB_TypeInfo_v1700__areaScope_r17__cond SIB_TypeInfo_v1700__areaScope_r17__Format.


Definition SIB_TypeInfo_v1700__Format_Type := Eval cbn in seq_format_prod SIB_TypeInfo_v1700__list.
Definition SIB_TypeInfo_v1700__Format_list : SIB_TypeInfo_v1700__Format_Type :=
  (SIB_TypeInfo_v1700__sibType_r17__Format, (SIB_TypeInfo_v1700__valueTag_r17__Format, (SIB_TypeInfo_v1700__areaScope_r17__Format, unit_format))).
Definition SIB_TypeInfo_v1700__list__Format := (*Eval compute in *) seq_format SIB_TypeInfo_v1700__list SIB_TypeInfo_v1700__Format_list.
Definition SIB_TypeInfo_v1700__F1 z :=
  (SIB_TypeInfo_v1700__sibType_r17 z, (SIB_TypeInfo_v1700__valueTag_r17 z, (SIB_TypeInfo_v1700__areaScope_r17 z, tt))).
Definition SIB_TypeInfo_v1700__F2 (y : seq_type SIB_TypeInfo_v1700__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SIB_TypeInfo_v1700__Type i0 i1 i2
  end.
Lemma SIB_TypeInfo_v1700__F1F2_cond (z : SIB_TypeInfo_v1700__Type)
  : SIB_TypeInfo_v1700__cond z ->
  (seq_cond SIB_TypeInfo_v1700__list (SIB_TypeInfo_v1700__F1 z)).
intro H. unfold SIB_TypeInfo_v1700__cond in H. simpl. auto. Qed.
Lemma SIB_TypeInfo_v1700__F1F2_cond2 (z : SIB_TypeInfo_v1700__Type)
 : SIB_TypeInfo_v1700__F2 (SIB_TypeInfo_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB_TypeInfo_v1700__F2F1_cond (y : seq_type SIB_TypeInfo_v1700__list)
  : seq_cond SIB_TypeInfo_v1700__list y ->
 (SIB_TypeInfo_v1700__cond (SIB_TypeInfo_v1700__F2 y)) /\  SIB_TypeInfo_v1700__F1 (SIB_TypeInfo_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB_TypeInfo_v1700__cond. simpl in *. auto.
 - simpl. unfold SIB_TypeInfo_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB_TypeInfo_v1700__Format : T_Format SIB_TypeInfo_v1700__Type SIB_TypeInfo_v1700__cond :=
        proj2_format  SIB_TypeInfo_v1700__cond SIB_TypeInfo_v1700__list__Format
    SIB_TypeInfo_v1700__F1 SIB_TypeInfo_v1700__F2 SIB_TypeInfo_v1700__F1F2_cond  SIB_TypeInfo_v1700__F1F2_cond2 SIB_TypeInfo_v1700__F2F1_cond.
Opaque SIB_TypeInfo_v1700__cond SIB_TypeInfo_v1700__Format.

