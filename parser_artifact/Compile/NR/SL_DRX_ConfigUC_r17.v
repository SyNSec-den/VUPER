Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__helper1 : (1 <= 31)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__helper2 : to_bit_sz (Z.to_nat (31 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__cond := (fun z => (1 <= z <= 31)%Z).
Inductive SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type : Set :=
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms2
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms3
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms4
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms5
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms6
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms8
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms10
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms20
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms30
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms40
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms50
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms60
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms80
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms100
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms200
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms300
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms400
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms500
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms600
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms800
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1000
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1200
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1600
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare8
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare7
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare6
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare5
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare4
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare3
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare2
 | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare1
.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__cond := (fun (_ : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type) => True).
Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__nat__helper.

Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F1 t :=
  match t with
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1 => 0
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms2 => 1
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms3 => 2
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms4 => 3
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms5 => 4
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms6 => 5
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms8 => 6
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms10 => 7
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms20 => 8
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms30 => 9
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms40 => 10
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms50 => 11
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms60 => 12
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms80 => 13
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms100 => 14
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms200 => 15
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms300 => 16
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms400 => 17
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms500 => 18
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms600 => 19
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms800 => 20
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1000 => 21
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1200 => 22
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1600 => 23
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare8 => 24
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare7 => 25
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare6 => 26
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare5 => 27
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare4 => 28
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare3 => 29
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare2 => 30
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare1 => 31
  end.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F2 n :=
  match n with
  | 0 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1
  | 1 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms2
  | 2 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms3
  | 3 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms4
  | 4 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms5
  | 5 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms6
  | 6 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms8
  | 7 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms10
  | 8 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms20
  | 9 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms30
  | 10 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms40
  | 11 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms50
  | 12 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms60
  | 13 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms80
  | 14 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms100
  | 15 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms200
  | 16 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms300
  | 17 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms400
  | 18 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms500
  | 19 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms600
  | 20 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms800
  | 21 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1000
  | 22 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1200
  | 23 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1600
  | 24 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare8
  | 25 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare7
  | 26 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare6
  | 27 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare5
  | 28 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare4
  | 29 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare3
  | 30 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare2
  | 31 => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__spare1
  | _ => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__ms1
  end.
Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F1F2 : forall x : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type, (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F1 x <= 31) /\ SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F2 (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F2F1 : forall (y : nat) (H : y <= 31), SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F1 (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F2 y) = y. enum_solve H y. Qed.


Inductive SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type : Set :=
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds : Z -> SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type -> SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type
.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list : list typ := (
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__cond ::
typ_cons SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__cond ::
 nil).
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__cond (c : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type) := 
  match c with
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds t => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds t => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__cond t 
  end.

Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__len_helper1 : to_bit_sz (length SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__len_helper2 : 2 <= length2 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list.
 simpl. lia. Qed.
Inductive SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Type : Set :=
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms0
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms2
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms3
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms4
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms5
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms6
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms8
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms10
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms20
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms30
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms40
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms50
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms60
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms80
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms100
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms200
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms300
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms500
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms750
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1280
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1920
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms2560
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare9
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare8
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare7
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare6
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare5
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare4
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare3
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare2
 | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare1
.
Definition SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__cond := (fun (_ : SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Type) => True).
Lemma SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__nat__helper.

Definition SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F1 t :=
  match t with
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms0 => 0
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1 => 1
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms2 => 2
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms3 => 3
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms4 => 4
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms5 => 5
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms6 => 6
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms8 => 7
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms10 => 8
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms20 => 9
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms30 => 10
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms40 => 11
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms50 => 12
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms60 => 13
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms80 => 14
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms100 => 15
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms200 => 16
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms300 => 17
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms500 => 18
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms750 => 19
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1280 => 20
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1920 => 21
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms2560 => 22
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare9 => 23
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare8 => 24
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare7 => 25
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare6 => 26
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare5 => 27
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare4 => 28
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare3 => 29
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare2 => 30
  | SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare1 => 31
  end.
Definition SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F2 n :=
  match n with
  | 0 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms0
  | 1 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1
  | 2 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms2
  | 3 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms3
  | 4 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms4
  | 5 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms5
  | 6 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms6
  | 7 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms8
  | 8 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms10
  | 9 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms20
  | 10 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms30
  | 11 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms40
  | 12 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms50
  | 13 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms60
  | 14 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms80
  | 15 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms100
  | 16 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms200
  | 17 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms300
  | 18 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms500
  | 19 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms750
  | 20 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1280
  | 21 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms1920
  | 22 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms2560
  | 23 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare9
  | 24 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare8
  | 25 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare7
  | 26 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare6
  | 27 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare5
  | 28 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare4
  | 29 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare3
  | 30 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare2
  | 31 => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__spare1
  | _ => SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__ms0
  end.
Lemma SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F1F2 : forall x : SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Type, (SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F1 x <= 31) /\ SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F2 (SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F2F1 : forall (y : nat) (H : y <= 31), SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F1 (SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Type : Set :=
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl0
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl1
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl2
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl4
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare4
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare3
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare2
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare1
.
Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__cond := (fun (_ : SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Type) => True).
Lemma SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__nat__helper.

Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F1 t :=
  match t with
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl0 => 0
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl1 => 1
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl2 => 2
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl4 => 3
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare4 => 4
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare3 => 5
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare2 => 6
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare1 => 7
  end.
Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F2 n :=
  match n with
  | 0 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl0
  | 1 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl1
  | 2 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl2
  | 3 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl4
  | 4 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare4
  | 5 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare3
  | 6 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare2
  | 7 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__spare1
  | _ => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__sl0
  end.
Lemma SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F1F2 : forall x : SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Type, (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F1 x <= 7) /\ SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F2 (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F2F1 : forall (y : nat) (H : y <= 7), SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F1 (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Type : Set :=
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl0
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl1
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl2
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl4
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare4
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare3
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare2
 | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare1
.
Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__cond := (fun (_ : SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Type) => True).
Lemma SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__nat__helper.

Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F1 t :=
  match t with
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl0 => 0
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl1 => 1
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl2 => 2
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl4 => 3
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare4 => 4
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare3 => 5
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare2 => 6
  | SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare1 => 7
  end.
Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F2 n :=
  match n with
  | 0 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl0
  | 1 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl1
  | 2 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl2
  | 3 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl4
  | 4 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare4
  | 5 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare3
  | 6 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare2
  | 7 => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__spare1
  | _ => SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__sl0
  end.
Lemma SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F1F2 : forall x : SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Type, (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F1 x <= 7) /\ SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F2 (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F2F1 : forall (y : nat) (H : y <= 7), SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F1 (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Type : Set :=
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl0
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl1
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl2
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl4
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl6
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl8
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl16
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl24
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl33
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl40
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl64
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl80
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl96
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl112
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl128
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl160
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl320
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare15
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare14
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare13
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare12
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare11
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare10
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare9
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare8
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare7
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare6
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare5
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare4
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare3
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare2
 | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare1
.
Definition SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__cond := (fun (_ : SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Type) => True).
Lemma SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__nat__helper.

Definition SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F1 t :=
  match t with
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl0 => 0
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl1 => 1
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl2 => 2
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl4 => 3
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl6 => 4
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl8 => 5
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl16 => 6
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl24 => 7
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl33 => 8
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl40 => 9
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl64 => 10
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl80 => 11
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl96 => 12
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl112 => 13
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl128 => 14
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl160 => 15
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl320 => 16
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare15 => 17
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare14 => 18
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare13 => 19
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare12 => 20
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare11 => 21
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare10 => 22
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare9 => 23
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare8 => 24
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare7 => 25
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare6 => 26
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare5 => 27
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare4 => 28
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare3 => 29
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare2 => 30
  | SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare1 => 31
  end.
Definition SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F2 n :=
  match n with
  | 0 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl0
  | 1 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl1
  | 2 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl2
  | 3 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl4
  | 4 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl6
  | 5 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl8
  | 6 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl16
  | 7 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl24
  | 8 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl33
  | 9 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl40
  | 10 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl64
  | 11 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl80
  | 12 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl96
  | 13 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl112
  | 14 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl128
  | 15 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl160
  | 16 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl320
  | 17 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare15
  | 18 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare14
  | 19 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare13
  | 20 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare12
  | 21 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare11
  | 22 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare10
  | 23 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare9
  | 24 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare8
  | 25 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare7
  | 26 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare6
  | 27 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare5
  | 28 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare4
  | 29 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare3
  | 30 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare2
  | 31 => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__spare1
  | _ => SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__sl0
  end.
Lemma SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F1F2 : forall x : SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Type, (SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F1 x <= 31) /\ SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F2 (SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F2F1 : forall (y : nat) (H : y <= 31), SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F1 (SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F2 y) = y. enum_solve H y. Qed.

Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__helper1 : (0 <= 59)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__helper2 : to_bit_sz (Z.to_nat (59 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (59 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__cond := (fun z => (0 <= z <= 59)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__helper1 : (0 <= 69)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__helper2 : to_bit_sz (Z.to_nat (69 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (69 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__cond := (fun z => (0 <= z <= 69)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__cond := (fun z => (0 <= z <= 255)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__helper1 : (0 <= 511)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__helper2 : to_bit_sz (Z.to_nat (511 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (511 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__cond := (fun z => (0 <= z <= 511)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__helper1 : (0 <= 2047)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__helper2 : to_bit_sz (Z.to_nat (2047 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2047 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__cond := (fun z => (0 <= z <= 2047)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__cond := (fun z => (0 <= z <= 10239)%Z).

Inductive SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type : Set :=
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240 : Z -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type
.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list : list typ := (
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__cond ::
typ_cons Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__cond ::
 nil).
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__cond (c : SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type) := 
  match c with
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__cond t 
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240 t => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__cond t 
  end.

Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__len_helper1 : to_bit_sz (length SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__len_helper2 : 2 <= length2 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list.
 simpl. lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__Type := Z.
Definition SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__cond := (fun z => (0 <= z <= 31)%Z).
Record SL_DRX_ConfigUC_r17__Type : Set :=
  make__SL_DRX_ConfigUC_r17__Type {
    SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17 : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type ;
    SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17 : SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Type ;
    SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17 : option SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Type ;
    SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17 : option SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Type ;
    SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17 : SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Type ;
    SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17 : SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type ;
    SL_DRX_ConfigUC_r17__sl_drx_SlotOffset : Z ;
}.
Definition SL_DRX_ConfigUC_r17__list := (
 Nor SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__cond ::
 Nor SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Type SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__cond ::
 Opt SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Type SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__cond ::
 Opt SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Type SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__cond ::
 Nor SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Type SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__cond ::
 Nor SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__cond ::
 Nor Z SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__cond ::
 nil).
Definition SL_DRX_ConfigUC_r17__cond z := 
  SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__cond (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17 z) /\
  SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__cond (SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17 z) /\
  opt_cond SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__cond (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17 z) /\
  opt_cond SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__cond (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17 z) /\
  SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__cond (SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17 z) /\
  SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__cond (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17 z) /\
  SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__cond (SL_DRX_ConfigUC_r17__sl_drx_SlotOffset z) /\
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
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__cond :=
 ranged_int_format (1) (31) SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__helper1 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__cond SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Format : T_Format SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__nat__Format SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F1 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F2 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F1F2 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__F2F1.

Opaque SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__cond SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Format.


Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Format_Type := Eval cbn in get_formats SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Format_list : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Format_Type :=
  (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds__Format, (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Format, unit__Format)).
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list__Format := Eval compute in choice_format SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__len_helper1 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__len_helper2  SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Format_list.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F1 (z : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type) : (choice SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list) :=
  match z with
   | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds t => existT _ 0 t
  | SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds t => existT _ 1 t
  end.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__g := (fun n => typ_set (get_nth_typ SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list n)).
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F2 (y : choice SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list) : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__g n -> SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type) with
    | 0 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__subMilliSeconds t 
    | 1 => fun (t : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds__Type) => SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__milliSeconds t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type with end) n0
           end t0).

Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__helper2 :  forall (y : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type), SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__cond y -> choice_cond SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__helper3 :  forall (y : SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type), SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F2 (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__helper4 : (forall b : choice SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list, choice_cond SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list b -> SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__cond (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F2 b) /\ SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F1 (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F1 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F2.
Definition SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Format : T_Format SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Type SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__cond :=
  (* Eval compute in *) proj2_format SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__cond SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__list__Format SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F1 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__F2 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__helper2 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__helper3 SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__helper4.
Opaque SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__cond SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Format : T_Format SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__nat__Format SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F1 SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F2 SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F1F2 SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__F2F1.

Opaque SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__cond SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Format : T_Format SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__nat__Format SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F1 SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F2 SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F1F2 SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__F2F1.

Opaque SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__cond SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Format : T_Format SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__nat__Format SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F1 SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F2 SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F1F2 SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__F2F1.

Opaque SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__cond SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Format : T_Format SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__nat__Format SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F1 SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F2 SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F1F2 SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__F2F1.

Opaque SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__cond SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__cond :=
 ranged_int_format (0) (9) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__cond :=
 ranged_int_format (0) (19) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__cond :=
 ranged_int_format (0) (31) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__cond :=
 ranged_int_format (0) (39) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__cond :=
 ranged_int_format (0) (59) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__cond :=
 ranged_int_format (0) (63) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__cond :=
 ranged_int_format (0) (69) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__cond :=
 ranged_int_format (0) (79) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__cond :=
 ranged_int_format (0) (127) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__cond :=
 ranged_int_format (0) (159) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__cond :=
 ranged_int_format (0) (255) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__cond :=
 ranged_int_format (0) (319) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__cond :=
 ranged_int_format (0) (511) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__cond :=
 ranged_int_format (0) (639) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__cond :=
 ranged_int_format (0) (1023) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__cond :=
 ranged_int_format (0) (1279) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__cond :=
 ranged_int_format (0) (2047) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__cond :=
 ranged_int_format (0) (2559) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__cond :=
 ranged_int_format (0) (5119) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__cond :=
 ranged_int_format (0) (10239) SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__Format.


Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Format_Type := Eval cbn in get_formats SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Format_list : SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Format_Type :=
  (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240__Format, unit__Format)))))))))))))))))))).
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list__Format := Eval compute in choice_format SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__len_helper1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__len_helper2  SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Format_list.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F1 (z : SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type) : (choice SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list) :=
  match z with
   | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10 t => existT _ 0 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20 t => existT _ 1 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32 t => existT _ 2 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40 t => existT _ 3 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60 t => existT _ 4 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64 t => existT _ 5 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70 t => existT _ 6 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80 t => existT _ 7 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128 t => existT _ 8 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160 t => existT _ 9 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256 t => existT _ 10 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320 t => existT _ 11 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512 t => existT _ 12 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640 t => existT _ 13 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024 t => existT _ 14 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280 t => existT _ 15 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048 t => existT _ 16 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560 t => existT _ 17 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120 t => existT _ 18 t
  | SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240 t => existT _ 19 t
  end.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__g := (fun n => typ_set (get_nth_typ SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list n)).
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F2 (y : choice SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list) : SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__g n -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type) with
    | 0 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10 t 
    | 1 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms20 t 
    | 2 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms32 t 
    | 3 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms40 t 
    | 4 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms60 t 
    | 5 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms64 t 
    | 6 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms70 t 
    | 7 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms80 t 
    | 8 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms128 t 
    | 9 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms160 t 
    | 10 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms256 t 
    | 11 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms320 t 
    | 12 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms512 t 
    | 13 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms640 t 
    | 14 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1024 t 
    | 15 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms1280 t 
    | 16 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2048 t 
    | 17 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms2560 t 
    | 18 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms5120 t 
    | 19 => fun (t : Z) => SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__ms10240 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0)))))))))))))))))))) => (fun (x' : nat) (t'' : SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))))))))))))) in match t' return SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type with end) n0
           end t0).

Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__helper2 :  forall (y : SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type), SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__cond y -> choice_cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__helper3 :  forall (y : SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type), SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F2 (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__helper4 : (forall b : choice SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list, choice_cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list b -> SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__cond (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F2 b) /\ SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F1 (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F2.
Definition SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Format : T_Format SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Type SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__cond :=
  (* Eval compute in *) proj2_format SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__list__Format SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F1 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__F2 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__helper2 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__helper3 SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__helper4.
Opaque SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__cond SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Format.

Definition SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__Format : T_Format Z SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__cond :=
 ranged_int_format (0) (31) SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__helper1 SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__helper2.

Opaque SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__cond SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__Format.


Definition SL_DRX_ConfigUC_r17__Format_Type := Eval cbn in seq_format_prod SL_DRX_ConfigUC_r17__list.
Definition SL_DRX_ConfigUC_r17__Format_list : SL_DRX_ConfigUC_r17__Format_Type :=
  (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17__Format, (SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17__Format, (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17__Format, (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17__Format, (SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17__Format, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17__Format, (SL_DRX_ConfigUC_r17__sl_drx_SlotOffset__Format, unit_format))))))).
Definition SL_DRX_ConfigUC_r17__list__Format := (*Eval compute in *) seq_format SL_DRX_ConfigUC_r17__list SL_DRX_ConfigUC_r17__Format_list.
Definition SL_DRX_ConfigUC_r17__F1 z :=
  (SL_DRX_ConfigUC_r17__sl_drx_onDurationTimer_r17 z, (SL_DRX_ConfigUC_r17__sl_drx_InactivityTimer_r17 z, (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer1_r17 z, (SL_DRX_ConfigUC_r17__sl_drx_HARQ_RTT_Timer2_r17 z, (SL_DRX_ConfigUC_r17__sl_drx_RetransmissionTimer_r17 z, (SL_DRX_ConfigUC_r17__sl_drx_CycleStartOffset_r17 z, (SL_DRX_ConfigUC_r17__sl_drx_SlotOffset z, tt))))))).
Definition SL_DRX_ConfigUC_r17__F2 (y : seq_type SL_DRX_ConfigUC_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__SL_DRX_ConfigUC_r17__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma SL_DRX_ConfigUC_r17__F1F2_cond (z : SL_DRX_ConfigUC_r17__Type)
  : SL_DRX_ConfigUC_r17__cond z ->
  (seq_cond SL_DRX_ConfigUC_r17__list (SL_DRX_ConfigUC_r17__F1 z)).
intro H. unfold SL_DRX_ConfigUC_r17__cond in H. simpl. auto. Qed.
Lemma SL_DRX_ConfigUC_r17__F1F2_cond2 (z : SL_DRX_ConfigUC_r17__Type)
 : SL_DRX_ConfigUC_r17__F2 (SL_DRX_ConfigUC_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_DRX_ConfigUC_r17__F2F1_cond (y : seq_type SL_DRX_ConfigUC_r17__list)
  : seq_cond SL_DRX_ConfigUC_r17__list y ->
 (SL_DRX_ConfigUC_r17__cond (SL_DRX_ConfigUC_r17__F2 y)) /\  SL_DRX_ConfigUC_r17__F1 (SL_DRX_ConfigUC_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_DRX_ConfigUC_r17__cond. simpl in *. auto.
 - simpl. unfold SL_DRX_ConfigUC_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_DRX_ConfigUC_r17__Format : T_Format SL_DRX_ConfigUC_r17__Type SL_DRX_ConfigUC_r17__cond :=
        proj2_format  SL_DRX_ConfigUC_r17__cond SL_DRX_ConfigUC_r17__list__Format
    SL_DRX_ConfigUC_r17__F1 SL_DRX_ConfigUC_r17__F2 SL_DRX_ConfigUC_r17__F1F2_cond  SL_DRX_ConfigUC_r17__F1F2_cond2 SL_DRX_ConfigUC_r17__F2F1_cond.
Opaque SL_DRX_ConfigUC_r17__cond SL_DRX_ConfigUC_r17__Format.

