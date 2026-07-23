Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__helper1 : (1 <= 31)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__helper2 : to_bit_sz (Z.to_nat (31 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__Type := Z.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__cond := (fun z => (1 <= z <= 31)%Z).
Inductive DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Type : Set :=
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms2
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms3
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms4
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms5
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms6
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms8
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms10
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms20
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms30
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms40
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms50
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms60
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms80
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms100
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms200
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms300
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms400
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms500
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms600
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms800
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1000
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1200
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1600
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare8
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare7
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare6
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare5
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare4
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare3
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare2
 | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare1
.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__cond := (fun (_ : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Type) => True).
Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__nat__helper.

Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F1 t :=
  match t with
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1 => 0
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms2 => 1
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms3 => 2
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms4 => 3
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms5 => 4
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms6 => 5
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms8 => 6
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms10 => 7
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms20 => 8
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms30 => 9
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms40 => 10
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms50 => 11
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms60 => 12
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms80 => 13
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms100 => 14
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms200 => 15
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms300 => 16
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms400 => 17
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms500 => 18
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms600 => 19
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms800 => 20
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1000 => 21
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1200 => 22
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1600 => 23
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare8 => 24
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare7 => 25
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare6 => 26
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare5 => 27
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare4 => 28
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare3 => 29
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare2 => 30
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare1 => 31
  end.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F2 n :=
  match n with
  | 0 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1
  | 1 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms2
  | 2 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms3
  | 3 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms4
  | 4 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms5
  | 5 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms6
  | 6 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms8
  | 7 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms10
  | 8 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms20
  | 9 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms30
  | 10 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms40
  | 11 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms50
  | 12 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms60
  | 13 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms80
  | 14 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms100
  | 15 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms200
  | 16 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms300
  | 17 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms400
  | 18 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms500
  | 19 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms600
  | 20 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms800
  | 21 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1000
  | 22 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1200
  | 23 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1600
  | 24 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare8
  | 25 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare7
  | 26 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare6
  | 27 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare5
  | 28 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare4
  | 29 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare3
  | 30 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare2
  | 31 => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__spare1
  | _ => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__ms1
  end.
Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F1F2 : forall x : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Type, (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F1 x <= 31) /\ DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F2 (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F1 x) = x. imp_solve. Qed.
Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F2F1 : forall (y : nat) (H : y <= 31), DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F1 (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F2 y) = y. enum_solve H y. Qed.


Inductive DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type : Set :=
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds : Z -> DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Type -> DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type
.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list : list typ := (
typ_cons Z DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__cond ::
typ_cons DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Type DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__cond ::
 nil).
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__cond (c : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type) := 
  match c with
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds t => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__cond t 
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds t => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__cond t 
  end.

Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__len_helper1 : to_bit_sz (length DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__len_helper2 : 2 <= length2 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list.
 simpl. lia. Qed.
Inductive DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Type : Set :=
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms0
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms2
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms3
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms4
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms5
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms6
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms8
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms10
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms20
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms30
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms40
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms50
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms60
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms80
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms100
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms200
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms300
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms500
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms750
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1280
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1920
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms2560
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare9
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare8
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare7
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare6
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare5
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare4
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare3
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare2
 | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare1
.
Definition DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__cond := (fun (_ : DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Type) => True).
Lemma DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__nat__helper.

Definition DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F1 t :=
  match t with
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms0 => 0
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1 => 1
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms2 => 2
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms3 => 3
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms4 => 4
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms5 => 5
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms6 => 6
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms8 => 7
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms10 => 8
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms20 => 9
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms30 => 10
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms40 => 11
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms50 => 12
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms60 => 13
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms80 => 14
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms100 => 15
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms200 => 16
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms300 => 17
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms500 => 18
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms750 => 19
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1280 => 20
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1920 => 21
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms2560 => 22
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare9 => 23
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare8 => 24
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare7 => 25
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare6 => 26
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare5 => 27
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare4 => 28
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare3 => 29
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare2 => 30
  | DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare1 => 31
  end.
Definition DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F2 n :=
  match n with
  | 0 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms0
  | 1 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1
  | 2 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms2
  | 3 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms3
  | 4 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms4
  | 5 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms5
  | 6 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms6
  | 7 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms8
  | 8 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms10
  | 9 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms20
  | 10 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms30
  | 11 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms40
  | 12 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms50
  | 13 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms60
  | 14 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms80
  | 15 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms100
  | 16 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms200
  | 17 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms300
  | 18 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms500
  | 19 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms750
  | 20 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1280
  | 21 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms1920
  | 22 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms2560
  | 23 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare9
  | 24 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare8
  | 25 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare7
  | 26 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare6
  | 27 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare5
  | 28 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare4
  | 29 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare3
  | 30 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare2
  | 31 => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__spare1
  | _ => DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__ms0
  end.
Lemma DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F1F2 : forall x : DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Type, (DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F1 x <= 31) /\ DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F2 (DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F1 x) = x. imp_solve. Qed.
Lemma DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F2F1 : forall (y : nat) (H : y <= 31), DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F1 (DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F2 y) = y. enum_solve H y. Qed.

Lemma DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__helper1 : (0 <= 56)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__helper2 : to_bit_sz (Z.to_nat (56 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (56 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__Type := Z.
Definition DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__cond := (fun z => (0 <= z <= 56)%Z).
Inductive DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Type : Set :=
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl0
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl1
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl2
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl4
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl6
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl8
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl16
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl24
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl33
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl40
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl64
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl80
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl96
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl112
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl128
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl160
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl320
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare15
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare14
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare13
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare12
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare11
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare10
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare9
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare8
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare7
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare6
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare5
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare4
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare3
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare2
 | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare1
.
Definition DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__cond := (fun (_ : DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Type) => True).
Lemma DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__nat__helper.

Definition DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F1 t :=
  match t with
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl0 => 0
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl1 => 1
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl2 => 2
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl4 => 3
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl6 => 4
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl8 => 5
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl16 => 6
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl24 => 7
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl33 => 8
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl40 => 9
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl64 => 10
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl80 => 11
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl96 => 12
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl112 => 13
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl128 => 14
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl160 => 15
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl320 => 16
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare15 => 17
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare14 => 18
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare13 => 19
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare12 => 20
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare11 => 21
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare10 => 22
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare9 => 23
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare8 => 24
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare7 => 25
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare6 => 26
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare5 => 27
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare4 => 28
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare3 => 29
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare2 => 30
  | DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare1 => 31
  end.
Definition DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F2 n :=
  match n with
  | 0 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl0
  | 1 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl1
  | 2 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl2
  | 3 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl4
  | 4 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl6
  | 5 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl8
  | 6 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl16
  | 7 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl24
  | 8 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl33
  | 9 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl40
  | 10 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl64
  | 11 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl80
  | 12 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl96
  | 13 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl112
  | 14 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl128
  | 15 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl160
  | 16 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl320
  | 17 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare15
  | 18 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare14
  | 19 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare13
  | 20 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare12
  | 21 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare11
  | 22 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare10
  | 23 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare9
  | 24 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare8
  | 25 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare7
  | 26 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare6
  | 27 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare5
  | 28 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare4
  | 29 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare3
  | 30 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare2
  | 31 => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__spare1
  | _ => DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__sl0
  end.
Lemma DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F1F2 : forall x : DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Type, (DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F1 x <= 31) /\ DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F2 (DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F1 x) = x. imp_solve. Qed.
Lemma DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F2F1 : forall (y : nat) (H : y <= 31), DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F1 (DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F2 y) = y. enum_solve H y. Qed.

Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__helper1 : (0 <= 59)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__helper2 : to_bit_sz (Z.to_nat (59 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (59 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__cond := (fun z => (0 <= z <= 59)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__helper1 : (0 <= 69)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__helper2 : to_bit_sz (Z.to_nat (69 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (69 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__cond := (fun z => (0 <= z <= 69)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__cond := (fun z => (0 <= z <= 255)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__helper1 : (0 <= 511)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__helper2 : to_bit_sz (Z.to_nat (511 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (511 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__cond := (fun z => (0 <= z <= 511)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__helper1 : (0 <= 2047)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__helper2 : to_bit_sz (Z.to_nat (2047 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2047 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__cond := (fun z => (0 <= z <= 2047)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__Type := Z.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__cond := (fun z => (0 <= z <= 10239)%Z).

Inductive DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type : Set :=
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240 : Z -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type
.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list : list typ := (
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__cond ::
typ_cons Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__cond ::
 nil).
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__cond (c : DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type) := 
  match c with
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__cond t 
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240 t => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__cond t 
  end.

Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__len_helper1 : to_bit_sz (length DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__len_helper2 : 2 <= length2 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list.
 simpl. lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__Type := Z.
Definition DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__cond := (fun z => (0 <= z <= 31)%Z).
Record DRX_ConfigPTM_r17__Type : Set :=
  make__DRX_ConfigPTM_r17__Type {
    DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17 : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type ;
    DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17 : DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Type ;
    DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17 : option Z ;
    DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17 : option DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Type ;
    DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17 : DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type ;
    DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17 : Z ;
}.
Definition DRX_ConfigPTM_r17__list := (
 Nor DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__cond ::
 Nor DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Type DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__cond ::
 Opt Z DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__cond ::
 Opt DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Type DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__cond ::
 Nor DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__cond ::
 Nor Z DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__cond ::
 nil).
Definition DRX_ConfigPTM_r17__cond z := 
  DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__cond (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17 z) /\
  DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__cond (DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17 z) /\
  opt_cond DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__cond (DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17 z) /\
  opt_cond DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__cond (DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17 z) /\
  DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__cond (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17 z) /\
  DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__cond (DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17 z) /\
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
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__Format : T_Format Z DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__cond :=
 ranged_int_format (1) (31) DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__helper1 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__helper2.

Opaque DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__cond DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__Format.

Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Format : T_Format DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__nat__Format DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F1 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F2 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F1F2 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__F2F1.

Opaque DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__cond DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Format.


Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Format_Type := Eval cbn in get_formats DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Format_list : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Format_Type :=
  (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds__Format, (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Format, unit__Format)).
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list__Format := Eval compute in choice_format DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__len_helper1 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__len_helper2  DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Format_list.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F1 (z : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type) : (choice DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list) :=
  match z with
   | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds t => existT _ 0 t
  | DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds t => existT _ 1 t
  end.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__g := (fun n => typ_set (get_nth_typ DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list n)).
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F2 (y : choice DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list) : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__g n -> DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type) with
    | 0 => fun (t : Z) => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__subMilliSeconds t 
    | 1 => fun (t : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds__Type) => DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__milliSeconds t 
 | (S (S n0)) => (fun (x' : nat) (t'' : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type with end) n0
           end t0).

Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__helper2 :  forall (y : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type), DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__cond y -> choice_cond DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__helper3 :  forall (y : DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type), DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F2 (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__helper4 : (forall b : choice DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list, choice_cond DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list b -> DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__cond (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F2 b) /\ DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F1 (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F1 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F2.
Definition DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Format : T_Format DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Type DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__cond :=
  (* Eval compute in *) proj2_format DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__cond DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__list__Format DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F1 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__F2 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__helper2 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__helper3 DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__helper4.
Opaque DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__cond DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Format.

Definition DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Format : T_Format DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__nat__Format DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F1 DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F2 DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F1F2 DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__F2F1.

Opaque DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__cond DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Format.

Definition DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__Format : T_Format Z DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__cond :=
 ranged_int_format (0) (56) DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__helper1 DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__helper2.

Opaque DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__cond DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__Format.

Definition DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Format : T_Format DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__nat__Format DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F1 DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F2 DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F1F2 DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__F2F1.

Opaque DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__cond DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__cond :=
 ranged_int_format (0) (9) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__cond :=
 ranged_int_format (0) (19) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__cond :=
 ranged_int_format (0) (31) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__cond :=
 ranged_int_format (0) (39) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__cond :=
 ranged_int_format (0) (59) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__cond :=
 ranged_int_format (0) (63) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__cond :=
 ranged_int_format (0) (69) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__cond :=
 ranged_int_format (0) (79) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__cond :=
 ranged_int_format (0) (127) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__cond :=
 ranged_int_format (0) (159) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__cond :=
 ranged_int_format (0) (255) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__cond :=
 ranged_int_format (0) (319) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__cond :=
 ranged_int_format (0) (511) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__cond :=
 ranged_int_format (0) (639) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__cond :=
 ranged_int_format (0) (1023) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__cond :=
 ranged_int_format (0) (1279) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__cond :=
 ranged_int_format (0) (2047) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__cond :=
 ranged_int_format (0) (2559) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__cond :=
 ranged_int_format (0) (5119) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__Format.

Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__Format : T_Format Z DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__cond :=
 ranged_int_format (0) (10239) DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__helper2.

Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__Format.


Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Format_Type := Eval cbn in get_formats DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Format_list : DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Format_Type :=
  (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240__Format, unit__Format)))))))))))))))))))).
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list__Format := Eval compute in choice_format DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__len_helper1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__len_helper2  DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Format_list.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F1 (z : DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type) : (choice DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list) :=
  match z with
   | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10 t => existT _ 0 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20 t => existT _ 1 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32 t => existT _ 2 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40 t => existT _ 3 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60 t => existT _ 4 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64 t => existT _ 5 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70 t => existT _ 6 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80 t => existT _ 7 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128 t => existT _ 8 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160 t => existT _ 9 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256 t => existT _ 10 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320 t => existT _ 11 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512 t => existT _ 12 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640 t => existT _ 13 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024 t => existT _ 14 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280 t => existT _ 15 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048 t => existT _ 16 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560 t => existT _ 17 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120 t => existT _ 18 t
  | DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240 t => existT _ 19 t
  end.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__g := (fun n => typ_set (get_nth_typ DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list n)).
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F2 (y : choice DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list) : DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__g n -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type) with
    | 0 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10 t 
    | 1 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms20 t 
    | 2 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms32 t 
    | 3 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms40 t 
    | 4 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms60 t 
    | 5 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms64 t 
    | 6 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms70 t 
    | 7 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms80 t 
    | 8 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms128 t 
    | 9 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms160 t 
    | 10 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms256 t 
    | 11 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms320 t 
    | 12 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms512 t 
    | 13 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms640 t 
    | 14 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1024 t 
    | 15 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms1280 t 
    | 16 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2048 t 
    | 17 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms2560 t 
    | 18 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms5120 t 
    | 19 => fun (t : Z) => DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__ms10240 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0)))))))))))))))))))) => (fun (x' : nat) (t'' : DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))))))))))))) in match t' return DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type with end) n0
           end t0).

Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__helper2 :  forall (y : DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type), DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__cond y -> choice_cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__helper3 :  forall (y : DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type), DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F2 (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__helper4 : (forall b : choice DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list, choice_cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list b -> DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__cond (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F2 b) /\ DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F1 (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F2.
Definition DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Format : T_Format DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Type DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__cond :=
  (* Eval compute in *) proj2_format DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__list__Format DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F1 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__F2 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__helper2 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__helper3 DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__helper4.
Opaque DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__cond DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Format.

Definition DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__Format : T_Format Z DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__cond :=
 ranged_int_format (0) (31) DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__helper1 DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__helper2.

Opaque DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__cond DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__Format.


Definition DRX_ConfigPTM_r17__Format_Type := Eval cbn in seq_format_prod DRX_ConfigPTM_r17__list.
Definition DRX_ConfigPTM_r17__Format_list : DRX_ConfigPTM_r17__Format_Type :=
  (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17__Format, (DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17__Format, (DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17__Format, (DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17__Format, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17__Format, (DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17__Format, unit_format)))))).
Definition DRX_ConfigPTM_r17__list__Format := (*Eval compute in *) seq_format DRX_ConfigPTM_r17__list DRX_ConfigPTM_r17__Format_list.
Definition DRX_ConfigPTM_r17__F1 z :=
  (DRX_ConfigPTM_r17__drx_onDurationTimerPTM_r17 z, (DRX_ConfigPTM_r17__drx_InactivityTimerPTM_r17 z, (DRX_ConfigPTM_r17__drx_HARQ_RTT_TimerDL_PTM_r17 z, (DRX_ConfigPTM_r17__drx_RetransmissionTimerDL_PTM_r17 z, (DRX_ConfigPTM_r17__drx_LongCycleStartOffsetPTM_r17 z, (DRX_ConfigPTM_r17__drx_SlotOffsetPTM_r17 z, tt)))))).
Definition DRX_ConfigPTM_r17__F2 (y : seq_type DRX_ConfigPTM_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__DRX_ConfigPTM_r17__Type i0 i1 i2 i3 i4 i5
  end.
Lemma DRX_ConfigPTM_r17__F1F2_cond (z : DRX_ConfigPTM_r17__Type)
  : DRX_ConfigPTM_r17__cond z ->
  (seq_cond DRX_ConfigPTM_r17__list (DRX_ConfigPTM_r17__F1 z)).
intro H. unfold DRX_ConfigPTM_r17__cond in H. simpl. auto. Qed.
Lemma DRX_ConfigPTM_r17__F1F2_cond2 (z : DRX_ConfigPTM_r17__Type)
 : DRX_ConfigPTM_r17__F2 (DRX_ConfigPTM_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DRX_ConfigPTM_r17__F2F1_cond (y : seq_type DRX_ConfigPTM_r17__list)
  : seq_cond DRX_ConfigPTM_r17__list y ->
 (DRX_ConfigPTM_r17__cond (DRX_ConfigPTM_r17__F2 y)) /\  DRX_ConfigPTM_r17__F1 (DRX_ConfigPTM_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DRX_ConfigPTM_r17__cond. simpl in *. auto.
 - simpl. unfold DRX_ConfigPTM_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DRX_ConfigPTM_r17__Format : T_Format DRX_ConfigPTM_r17__Type DRX_ConfigPTM_r17__cond :=
        proj2_format  DRX_ConfigPTM_r17__cond DRX_ConfigPTM_r17__list__Format
    DRX_ConfigPTM_r17__F1 DRX_ConfigPTM_r17__F2 DRX_ConfigPTM_r17__F1F2_cond  DRX_ConfigPTM_r17__F1F2_cond2 DRX_ConfigPTM_r17__F2F1_cond.
Opaque DRX_ConfigPTM_r17__cond DRX_ConfigPTM_r17__Format.

