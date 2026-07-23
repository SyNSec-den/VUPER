Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type : Set :=
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms0
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms2
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms3
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms4
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms5
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms6
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms8
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms10
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms20
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms30
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms40
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms50
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms60
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms80
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms100
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms200
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms300
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms500
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms750
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1280
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1920
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms2560
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare9
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare8
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare7
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare6
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare5
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare4
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare3
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare2
 | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare1
.
Definition DRX_Preference_r16__preferredDRX_InactivityTimer_r16__cond := (fun (_ : DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type) => True).
Lemma DRX_Preference_r16__preferredDRX_InactivityTimer_r16__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_Preference_r16__preferredDRX_InactivityTimer_r16__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_Preference_r16__preferredDRX_InactivityTimer_r16__nat__helper.

Definition DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F1 t :=
  match t with
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms0 => 0
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1 => 1
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms2 => 2
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms3 => 3
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms4 => 4
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms5 => 5
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms6 => 6
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms8 => 7
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms10 => 8
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms20 => 9
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms30 => 10
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms40 => 11
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms50 => 12
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms60 => 13
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms80 => 14
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms100 => 15
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms200 => 16
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms300 => 17
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms500 => 18
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms750 => 19
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1280 => 20
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1920 => 21
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms2560 => 22
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare9 => 23
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare8 => 24
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare7 => 25
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare6 => 26
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare5 => 27
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare4 => 28
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare3 => 29
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare2 => 30
  | DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare1 => 31
  end.
Definition DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F2 n :=
  match n with
  | 0 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms0
  | 1 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1
  | 2 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms2
  | 3 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms3
  | 4 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms4
  | 5 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms5
  | 6 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms6
  | 7 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms8
  | 8 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms10
  | 9 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms20
  | 10 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms30
  | 11 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms40
  | 12 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms50
  | 13 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms60
  | 14 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms80
  | 15 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms100
  | 16 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms200
  | 17 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms300
  | 18 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms500
  | 19 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms750
  | 20 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1280
  | 21 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms1920
  | 22 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms2560
  | 23 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare9
  | 24 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare8
  | 25 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare7
  | 26 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare6
  | 27 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare5
  | 28 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare4
  | 29 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare3
  | 30 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare2
  | 31 => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__spare1
  | _ => DRX_Preference_r16__preferredDRX_InactivityTimer_r16__ms0
  end.
Lemma DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F1F2 : forall x : DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type, (DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F1 x <= 31) /\ DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F2 (DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F1 x) = x. imp_solve. Qed.
Lemma DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F2F1 : forall (y : nat) (H : y <= 31), DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F1 (DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F2 y) = y. enum_solve H y. Qed.

Inductive DRX_Preference_r16__preferredDRX_LongCycle_r16__Type : Set :=
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms20
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms32
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms40
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms60
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms64
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms70
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms80
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms128
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms160
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms256
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms320
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms512
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms640
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms1024
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms1280
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms2048
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms2560
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms5120
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10240
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare12
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare11
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare10
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare9
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare8
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare7
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare6
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare5
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare4
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare3
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare2
 | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare1
.
Definition DRX_Preference_r16__preferredDRX_LongCycle_r16__cond := (fun (_ : DRX_Preference_r16__preferredDRX_LongCycle_r16__Type) => True).
Lemma DRX_Preference_r16__preferredDRX_LongCycle_r16__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_Preference_r16__preferredDRX_LongCycle_r16__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_Preference_r16__preferredDRX_LongCycle_r16__nat__helper.

Definition DRX_Preference_r16__preferredDRX_LongCycle_r16__F1 t :=
  match t with
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10 => 0
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms20 => 1
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms32 => 2
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms40 => 3
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms60 => 4
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms64 => 5
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms70 => 6
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms80 => 7
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms128 => 8
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms160 => 9
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms256 => 10
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms320 => 11
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms512 => 12
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms640 => 13
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms1024 => 14
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms1280 => 15
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms2048 => 16
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms2560 => 17
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms5120 => 18
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10240 => 19
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare12 => 20
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare11 => 21
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare10 => 22
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare9 => 23
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare8 => 24
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare7 => 25
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare6 => 26
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare5 => 27
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare4 => 28
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare3 => 29
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare2 => 30
  | DRX_Preference_r16__preferredDRX_LongCycle_r16__spare1 => 31
  end.
Definition DRX_Preference_r16__preferredDRX_LongCycle_r16__F2 n :=
  match n with
  | 0 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10
  | 1 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms20
  | 2 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms32
  | 3 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms40
  | 4 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms60
  | 5 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms64
  | 6 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms70
  | 7 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms80
  | 8 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms128
  | 9 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms160
  | 10 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms256
  | 11 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms320
  | 12 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms512
  | 13 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms640
  | 14 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms1024
  | 15 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms1280
  | 16 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms2048
  | 17 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms2560
  | 18 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms5120
  | 19 => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10240
  | 20 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare12
  | 21 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare11
  | 22 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare10
  | 23 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare9
  | 24 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare8
  | 25 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare7
  | 26 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare6
  | 27 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare5
  | 28 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare4
  | 29 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare3
  | 30 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare2
  | 31 => DRX_Preference_r16__preferredDRX_LongCycle_r16__spare1
  | _ => DRX_Preference_r16__preferredDRX_LongCycle_r16__ms10
  end.
Lemma DRX_Preference_r16__preferredDRX_LongCycle_r16__F1F2 : forall x : DRX_Preference_r16__preferredDRX_LongCycle_r16__Type, (DRX_Preference_r16__preferredDRX_LongCycle_r16__F1 x <= 31) /\ DRX_Preference_r16__preferredDRX_LongCycle_r16__F2 (DRX_Preference_r16__preferredDRX_LongCycle_r16__F1 x) = x. imp_solve. Qed.
Lemma DRX_Preference_r16__preferredDRX_LongCycle_r16__F2F1 : forall (y : nat) (H : y <= 31), DRX_Preference_r16__preferredDRX_LongCycle_r16__F1 (DRX_Preference_r16__preferredDRX_LongCycle_r16__F2 y) = y. enum_solve H y. Qed.

Inductive DRX_Preference_r16__preferredDRX_ShortCycle_r16__Type : Set :=
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms2
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms3
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms4
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms5
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms6
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms7
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms8
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms10
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms14
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms16
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms20
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms30
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms32
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms35
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms40
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms64
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms80
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms128
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms160
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms256
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms320
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms512
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms640
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare9
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare8
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare7
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare6
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare5
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare4
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare3
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare2
 | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare1
.
Definition DRX_Preference_r16__preferredDRX_ShortCycle_r16__cond := (fun (_ : DRX_Preference_r16__preferredDRX_ShortCycle_r16__Type) => True).
Lemma DRX_Preference_r16__preferredDRX_ShortCycle_r16__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_Preference_r16__preferredDRX_ShortCycle_r16__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_Preference_r16__preferredDRX_ShortCycle_r16__nat__helper.

Definition DRX_Preference_r16__preferredDRX_ShortCycle_r16__F1 t :=
  match t with
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms2 => 0
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms3 => 1
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms4 => 2
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms5 => 3
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms6 => 4
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms7 => 5
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms8 => 6
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms10 => 7
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms14 => 8
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms16 => 9
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms20 => 10
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms30 => 11
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms32 => 12
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms35 => 13
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms40 => 14
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms64 => 15
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms80 => 16
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms128 => 17
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms160 => 18
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms256 => 19
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms320 => 20
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms512 => 21
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms640 => 22
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare9 => 23
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare8 => 24
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare7 => 25
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare6 => 26
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare5 => 27
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare4 => 28
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare3 => 29
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare2 => 30
  | DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare1 => 31
  end.
Definition DRX_Preference_r16__preferredDRX_ShortCycle_r16__F2 n :=
  match n with
  | 0 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms2
  | 1 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms3
  | 2 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms4
  | 3 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms5
  | 4 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms6
  | 5 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms7
  | 6 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms8
  | 7 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms10
  | 8 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms14
  | 9 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms16
  | 10 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms20
  | 11 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms30
  | 12 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms32
  | 13 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms35
  | 14 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms40
  | 15 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms64
  | 16 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms80
  | 17 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms128
  | 18 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms160
  | 19 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms256
  | 20 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms320
  | 21 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms512
  | 22 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms640
  | 23 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare9
  | 24 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare8
  | 25 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare7
  | 26 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare6
  | 27 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare5
  | 28 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare4
  | 29 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare3
  | 30 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare2
  | 31 => DRX_Preference_r16__preferredDRX_ShortCycle_r16__spare1
  | _ => DRX_Preference_r16__preferredDRX_ShortCycle_r16__ms2
  end.
Lemma DRX_Preference_r16__preferredDRX_ShortCycle_r16__F1F2 : forall x : DRX_Preference_r16__preferredDRX_ShortCycle_r16__Type, (DRX_Preference_r16__preferredDRX_ShortCycle_r16__F1 x <= 31) /\ DRX_Preference_r16__preferredDRX_ShortCycle_r16__F2 (DRX_Preference_r16__preferredDRX_ShortCycle_r16__F1 x) = x. imp_solve. Qed.
Lemma DRX_Preference_r16__preferredDRX_ShortCycle_r16__F2F1 : forall (y : nat) (H : y <= 31), DRX_Preference_r16__preferredDRX_ShortCycle_r16__F1 (DRX_Preference_r16__preferredDRX_ShortCycle_r16__F2 y) = y. enum_solve H y. Qed.

Lemma DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__Type := Z.
Definition DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__cond := (fun z => (1 <= z <= 16)%Z).
Record DRX_Preference_r16__Type : Set :=
  make__DRX_Preference_r16__Type {
    DRX_Preference_r16__preferredDRX_InactivityTimer_r16 : option DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type ;
    DRX_Preference_r16__preferredDRX_LongCycle_r16 : option DRX_Preference_r16__preferredDRX_LongCycle_r16__Type ;
    DRX_Preference_r16__preferredDRX_ShortCycle_r16 : option DRX_Preference_r16__preferredDRX_ShortCycle_r16__Type ;
    DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16 : option Z ;
}.
Definition DRX_Preference_r16__list := (
 Opt DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type DRX_Preference_r16__preferredDRX_InactivityTimer_r16__cond ::
 Opt DRX_Preference_r16__preferredDRX_LongCycle_r16__Type DRX_Preference_r16__preferredDRX_LongCycle_r16__cond ::
 Opt DRX_Preference_r16__preferredDRX_ShortCycle_r16__Type DRX_Preference_r16__preferredDRX_ShortCycle_r16__cond ::
 Opt Z DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__cond ::
 nil).
Definition DRX_Preference_r16__cond z := 
  opt_cond DRX_Preference_r16__preferredDRX_InactivityTimer_r16__cond (DRX_Preference_r16__preferredDRX_InactivityTimer_r16 z) /\
  opt_cond DRX_Preference_r16__preferredDRX_LongCycle_r16__cond (DRX_Preference_r16__preferredDRX_LongCycle_r16 z) /\
  opt_cond DRX_Preference_r16__preferredDRX_ShortCycle_r16__cond (DRX_Preference_r16__preferredDRX_ShortCycle_r16 z) /\
  opt_cond DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__cond (DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16 z) /\
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
Definition DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Format : T_Format DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_Preference_r16__preferredDRX_InactivityTimer_r16__nat__Format DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F1 DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F2 DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F1F2 DRX_Preference_r16__preferredDRX_InactivityTimer_r16__F2F1.

Opaque DRX_Preference_r16__preferredDRX_InactivityTimer_r16__cond DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Format.

Definition DRX_Preference_r16__preferredDRX_LongCycle_r16__Format : T_Format DRX_Preference_r16__preferredDRX_LongCycle_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_Preference_r16__preferredDRX_LongCycle_r16__nat__Format DRX_Preference_r16__preferredDRX_LongCycle_r16__F1 DRX_Preference_r16__preferredDRX_LongCycle_r16__F2 DRX_Preference_r16__preferredDRX_LongCycle_r16__F1F2 DRX_Preference_r16__preferredDRX_LongCycle_r16__F2F1.

Opaque DRX_Preference_r16__preferredDRX_LongCycle_r16__cond DRX_Preference_r16__preferredDRX_LongCycle_r16__Format.

Definition DRX_Preference_r16__preferredDRX_ShortCycle_r16__Format : T_Format DRX_Preference_r16__preferredDRX_ShortCycle_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_Preference_r16__preferredDRX_ShortCycle_r16__nat__Format DRX_Preference_r16__preferredDRX_ShortCycle_r16__F1 DRX_Preference_r16__preferredDRX_ShortCycle_r16__F2 DRX_Preference_r16__preferredDRX_ShortCycle_r16__F1F2 DRX_Preference_r16__preferredDRX_ShortCycle_r16__F2F1.

Opaque DRX_Preference_r16__preferredDRX_ShortCycle_r16__cond DRX_Preference_r16__preferredDRX_ShortCycle_r16__Format.

Definition DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__Format : T_Format Z DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__cond :=
 ranged_int_format (1) (16) DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__helper1 DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__helper2.

Opaque DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__cond DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__Format.


Definition DRX_Preference_r16__Format_Type := Eval cbn in seq_format_prod DRX_Preference_r16__list.
Definition DRX_Preference_r16__Format_list : DRX_Preference_r16__Format_Type :=
  (DRX_Preference_r16__preferredDRX_InactivityTimer_r16__Format, (DRX_Preference_r16__preferredDRX_LongCycle_r16__Format, (DRX_Preference_r16__preferredDRX_ShortCycle_r16__Format, (DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16__Format, unit_format)))).
Definition DRX_Preference_r16__list__Format := (*Eval compute in *) seq_format DRX_Preference_r16__list DRX_Preference_r16__Format_list.
Definition DRX_Preference_r16__F1 z :=
  (DRX_Preference_r16__preferredDRX_InactivityTimer_r16 z, (DRX_Preference_r16__preferredDRX_LongCycle_r16 z, (DRX_Preference_r16__preferredDRX_ShortCycle_r16 z, (DRX_Preference_r16__preferredDRX_ShortCycleTimer_r16 z, tt)))).
Definition DRX_Preference_r16__F2 (y : seq_type DRX_Preference_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__DRX_Preference_r16__Type i0 i1 i2 i3
  end.
Lemma DRX_Preference_r16__F1F2_cond (z : DRX_Preference_r16__Type)
  : DRX_Preference_r16__cond z ->
  (seq_cond DRX_Preference_r16__list (DRX_Preference_r16__F1 z)).
intro H. unfold DRX_Preference_r16__cond in H. simpl. auto. Qed.
Lemma DRX_Preference_r16__F1F2_cond2 (z : DRX_Preference_r16__Type)
 : DRX_Preference_r16__F2 (DRX_Preference_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRX_Preference_r16__F2F1_cond (y : seq_type DRX_Preference_r16__list)
  : seq_cond DRX_Preference_r16__list y ->
 (DRX_Preference_r16__cond (DRX_Preference_r16__F2 y)) /\  DRX_Preference_r16__F1 (DRX_Preference_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRX_Preference_r16__cond. simpl in *. auto.
 - simpl. unfold DRX_Preference_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRX_Preference_r16__Format : T_Format DRX_Preference_r16__Type DRX_Preference_r16__cond :=
        proj2_format  DRX_Preference_r16__cond DRX_Preference_r16__list__Format
    DRX_Preference_r16__F1 DRX_Preference_r16__F2 DRX_Preference_r16__F1F2_cond  DRX_Preference_r16__F1F2_cond2 DRX_Preference_r16__F2F1_cond.
Opaque DRX_Preference_r16__cond DRX_Preference_r16__Format.

