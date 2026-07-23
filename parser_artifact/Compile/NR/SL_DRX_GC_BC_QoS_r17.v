Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_QoS_Profile_r16.

Opaque SL_QoS_Profile_r16__cond SL_QoS_Profile_r16__Format.

Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__Type := list SL_QoS_Profile_r16__Type.

Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__helper1 : (0 <= 1 <= maxNrofSL_QFIs_r16)%Z. unfold maxNrofSL_QFIs_r16.
 lia. Qed.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_QFIs_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_QFIs_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__cond (z : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_QFIs_r16)%Z /\ (list_and SL_QoS_Profile_r16__cond z) .

Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__helper1 : (1 <= 31)%Z.  lia. Qed.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__helper2 : to_bit_sz (Z.to_nat (31 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__Type := Z.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__cond := (fun z => (1 <= z <= 31)%Z).
Inductive SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Type : Set :=
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms2
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms3
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms4
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms5
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms6
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms8
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms10
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms20
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms30
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms40
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms50
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms60
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms80
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms100
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms200
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms300
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms400
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms500
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms600
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms800
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1000
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1200
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1600
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare8
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare7
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare6
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare5
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare4
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare3
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare2
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare1
.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__cond := (fun (_ : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Type) => True).
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__nat__helper.

Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F1 t :=
  match t with
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1 => 0
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms2 => 1
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms3 => 2
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms4 => 3
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms5 => 4
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms6 => 5
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms8 => 6
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms10 => 7
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms20 => 8
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms30 => 9
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms40 => 10
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms50 => 11
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms60 => 12
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms80 => 13
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms100 => 14
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms200 => 15
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms300 => 16
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms400 => 17
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms500 => 18
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms600 => 19
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms800 => 20
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1000 => 21
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1200 => 22
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1600 => 23
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare8 => 24
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare7 => 25
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare6 => 26
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare5 => 27
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare4 => 28
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare3 => 29
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare2 => 30
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare1 => 31
  end.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F2 n :=
  match n with
  | 0 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1
  | 1 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms2
  | 2 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms3
  | 3 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms4
  | 4 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms5
  | 5 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms6
  | 6 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms8
  | 7 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms10
  | 8 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms20
  | 9 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms30
  | 10 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms40
  | 11 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms50
  | 12 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms60
  | 13 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms80
  | 14 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms100
  | 15 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms200
  | 16 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms300
  | 17 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms400
  | 18 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms500
  | 19 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms600
  | 20 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms800
  | 21 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1000
  | 22 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1200
  | 23 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1600
  | 24 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare8
  | 25 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare7
  | 26 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare6
  | 27 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare5
  | 28 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare4
  | 29 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare3
  | 30 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare2
  | 31 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__spare1
  | _ => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__ms1
  end.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F1F2 : forall x : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Type, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F1 x <= 31) /\ SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F2 (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F2F1 : forall (y : nat) (H : y <= 31), SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F1 (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F2 y) = y. enum_solve H y. Qed.


Inductive SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type : Set :=
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds : Z -> SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Type -> SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type
.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list : list typ := (
typ_cons Z SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__cond ::
typ_cons SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Type SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__cond ::
 nil).
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__cond (c : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type) := 
  match c with
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds t => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__cond t 
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds t => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__cond t 
  end.

Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__len_helper1 : to_bit_sz (length SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__len_helper2 : 2 <= length2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list.
 simpl. lia. Qed.
Inductive SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Type : Set :=
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms0
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms2
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms3
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms4
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms5
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms6
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms8
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms10
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms20
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms30
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms40
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms50
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms60
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms80
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms100
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms200
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms300
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms500
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms750
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1280
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1920
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms2560
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare9
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare8
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare7
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare6
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare5
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare4
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare3
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare2
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare1
.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__cond := (fun (_ : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Type) => True).
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__nat__helper.

Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F1 t :=
  match t with
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms0 => 0
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1 => 1
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms2 => 2
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms3 => 3
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms4 => 4
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms5 => 5
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms6 => 6
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms8 => 7
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms10 => 8
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms20 => 9
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms30 => 10
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms40 => 11
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms50 => 12
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms60 => 13
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms80 => 14
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms100 => 15
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms200 => 16
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms300 => 17
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms500 => 18
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms750 => 19
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1280 => 20
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1920 => 21
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms2560 => 22
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare9 => 23
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare8 => 24
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare7 => 25
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare6 => 26
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare5 => 27
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare4 => 28
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare3 => 29
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare2 => 30
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare1 => 31
  end.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F2 n :=
  match n with
  | 0 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms0
  | 1 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1
  | 2 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms2
  | 3 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms3
  | 4 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms4
  | 5 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms5
  | 6 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms6
  | 7 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms8
  | 8 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms10
  | 9 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms20
  | 10 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms30
  | 11 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms40
  | 12 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms50
  | 13 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms60
  | 14 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms80
  | 15 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms100
  | 16 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms200
  | 17 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms300
  | 18 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms500
  | 19 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms750
  | 20 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1280
  | 21 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms1920
  | 22 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms2560
  | 23 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare9
  | 24 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare8
  | 25 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare7
  | 26 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare6
  | 27 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare5
  | 28 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare4
  | 29 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare3
  | 30 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare2
  | 31 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__spare1
  | _ => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__ms0
  end.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F1F2 : forall x : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Type, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F1 x <= 31) /\ SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F2 (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F2F1 : forall (y : nat) (H : y <= 31), SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F1 (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Type : Set :=
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms10
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms20
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms32
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms40
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms60
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms64
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms70
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms80
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms128
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms160
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms256
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms320
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms512
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms640
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms1024
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms1280
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms2048
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms2560
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms5120
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms10240
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare12
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare11
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare10
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare9
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare8
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare7
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare6
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare5
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare4
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare3
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare2
 | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare1
.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__cond := (fun (_ : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Type) => True).
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__nat__helper.

Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F1 t :=
  match t with
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms10 => 0
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms20 => 1
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms32 => 2
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms40 => 3
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms60 => 4
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms64 => 5
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms70 => 6
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms80 => 7
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms128 => 8
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms160 => 9
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms256 => 10
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms320 => 11
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms512 => 12
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms640 => 13
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms1024 => 14
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms1280 => 15
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms2048 => 16
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms2560 => 17
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms5120 => 18
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms10240 => 19
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare12 => 20
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare11 => 21
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare10 => 22
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare9 => 23
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare8 => 24
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare7 => 25
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare6 => 26
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare5 => 27
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare4 => 28
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare3 => 29
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare2 => 30
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare1 => 31
  end.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F2 n :=
  match n with
  | 0 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms10
  | 1 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms20
  | 2 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms32
  | 3 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms40
  | 4 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms60
  | 5 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms64
  | 6 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms70
  | 7 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms80
  | 8 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms128
  | 9 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms160
  | 10 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms256
  | 11 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms320
  | 12 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms512
  | 13 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms640
  | 14 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms1024
  | 15 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms1280
  | 16 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms2048
  | 17 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms2560
  | 18 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms5120
  | 19 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms10240
  | 20 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare12
  | 21 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare11
  | 22 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare10
  | 23 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare9
  | 24 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare8
  | 25 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare7
  | 26 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare6
  | 27 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare5
  | 28 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare4
  | 29 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare3
  | 30 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare2
  | 31 => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__spare1
  | _ => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__ms10
  end.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F1F2 : forall x : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Type, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F1 x <= 31) /\ SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F2 (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F2F1 : forall (y : nat) (H : y <= 31), SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F1 (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F2 y) = y. enum_solve H y. Qed.

Record SL_DRX_GC_BC_QoS_r17__Type : Set :=
  make__SL_DRX_GC_BC_QoS_r17__Type {
    SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17 : option SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__Type ;
    SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17 : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type ;
    SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17 : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Type ;
    SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17 : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Type ;
}.
Definition SL_DRX_GC_BC_QoS_r17__root_list : list seq_elem := (
 Opt SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__Type SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__cond ::
 Nor SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__cond ::
 Nor SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Type SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__cond ::
 Nor SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Type SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__cond ::
 nil).
Definition SL_DRX_GC_BC_QoS_r17__ext_list : list typ := (
  nil).
Definition SL_DRX_GC_BC_QoS_r17__cond (z : SL_DRX_GC_BC_QoS_r17__Type) := 
(  opt_cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__cond (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17 z) /\
  SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__cond (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17 z) /\
  SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__cond (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17 z) /\
  SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__cond (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17 z) /\
  True) /\ 
(  True).


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
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__Format : T_Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__Type SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__cond := seq_of_format SL_QoS_Profile_r16__Format 1 maxNrofSL_QFIs_r16 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__helper1 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__helper2.

Opaque SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__Format.

Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__Format : T_Format Z SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__cond :=
 ranged_int_format (1) (31) SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__helper1 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__helper2.

Opaque SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__Format.

Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Format : T_Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__nat__Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F1 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F1F2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__F2F1.

Opaque SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Format.


Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Format_Type := Eval cbn in get_formats SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Format_list : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Format_Type :=
  (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds__Format, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Format, unit__Format)).
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list__Format := Eval compute in choice_format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__len_helper1 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__len_helper2  SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Format_list.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F1 (z : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type) : (choice SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list) :=
  match z with
   | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds t => existT _ 0 t
  | SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds t => existT _ 1 t
  end.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__g := (fun n => typ_set (get_nth_typ SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list n)).
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F2 (y : choice SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list) : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__g n -> SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type) with
    | 0 => fun (t : Z) => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__subMilliSeconds t 
    | 1 => fun (t : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds__Type) => SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__milliSeconds t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type with end) n0
           end t0).

Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__helper2 :  forall (y : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type), SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__cond y -> choice_cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__helper3 :  forall (y : SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type), SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F2 (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__helper4 : (forall b : choice SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list, choice_cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list b -> SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__cond (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F2 b) /\ SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F1 (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F1 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F2.
Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Format : T_Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Type SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__cond :=
  (* Eval compute in *) proj2_format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__list__Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F1 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__F2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__helper2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__helper3 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__helper4.
Opaque SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Format.

Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Format : T_Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__nat__Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F1 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F1F2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__F2F1.

Opaque SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Format.

Definition SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Format : T_Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__nat__Format SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F1 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F1F2 SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__F2F1.

Opaque SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__cond SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Format.


Definition SL_DRX_GC_BC_QoS_r17__root_Format_Type := Eval cbn in seq_format_prod SL_DRX_GC_BC_QoS_r17__root_list.
Definition SL_DRX_GC_BC_QoS_r17__root_Format_list : SL_DRX_GC_BC_QoS_r17__root_Format_Type :=
  (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17__Format, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17__Format, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17__Format, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17__Format, unit_format)))).

Definition SL_DRX_GC_BC_QoS_r17__ext_Format_Type := Eval cbn in get_formats SL_DRX_GC_BC_QoS_r17__ext_list.
Definition SL_DRX_GC_BC_QoS_r17__ext_Format_list : SL_DRX_GC_BC_QoS_r17__ext_Format_Type :=
  unit__Format.

Definition SL_DRX_GC_BC_QoS_r17__list_type : Set := (seq_type SL_DRX_GC_BC_QoS_r17__root_list) * (seq_ext_type SL_DRX_GC_BC_QoS_r17__ext_list).
Definition SL_DRX_GC_BC_QoS_r17__list_cond (z : SL_DRX_GC_BC_QoS_r17__list_type) : Prop :=
        (seq_cond SL_DRX_GC_BC_QoS_r17__root_list (fst z)) /\ (seq_ext_cond SL_DRX_GC_BC_QoS_r17__ext_list (snd z)).
Definition SL_DRX_GC_BC_QoS_r17__list_format : T_Format SL_DRX_GC_BC_QoS_r17__list_type SL_DRX_GC_BC_QoS_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SL_DRX_GC_BC_QoS_r17__root_list SL_DRX_GC_BC_QoS_r17__root_Format_list SL_DRX_GC_BC_QoS_r17__ext_list SL_DRX_GC_BC_QoS_r17__ext_Format_list.

Opaque SL_DRX_GC_BC_QoS_r17__list_format.
Definition SL_DRX_GC_BC_QoS_r17__F1 (z : SL_DRX_GC_BC_QoS_r17__Type) : SL_DRX_GC_BC_QoS_r17__list_type :=
  (((SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_MappedQoS_FlowList_r17 z, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_OnDurationTimer_r17 z, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_InactivityTimer_r17 z, (SL_DRX_GC_BC_QoS_r17__sl_DRX_GC_BC_Cycle_r17 z, tt))))), (
tt)).
Definition SL_DRX_GC_BC_QoS_r17__F2 (y : SL_DRX_GC_BC_QoS_r17__list_type) : SL_DRX_GC_BC_QoS_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SL_DRX_GC_BC_QoS_r17__Type j0 j1 j2 j3
  end.
Definition SL_DRX_GC_BC_QoS_r17__helper1 : (forall a : SL_DRX_GC_BC_QoS_r17__Type, SL_DRX_GC_BC_QoS_r17__cond a -> SL_DRX_GC_BC_QoS_r17__list_cond (SL_DRX_GC_BC_QoS_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_DRX_GC_BC_QoS_r17__helper2 : (forall a : SL_DRX_GC_BC_QoS_r17__Type, SL_DRX_GC_BC_QoS_r17__F2 (SL_DRX_GC_BC_QoS_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_DRX_GC_BC_QoS_r17__helper3 : (forall b : SL_DRX_GC_BC_QoS_r17__list_type, SL_DRX_GC_BC_QoS_r17__list_cond b -> SL_DRX_GC_BC_QoS_r17__cond (SL_DRX_GC_BC_QoS_r17__F2 b) /\ SL_DRX_GC_BC_QoS_r17__F1 (SL_DRX_GC_BC_QoS_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_DRX_GC_BC_QoS_r17__cond, SL_DRX_GC_BC_QoS_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_DRX_GC_BC_QoS_r17__Format : T_Format SL_DRX_GC_BC_QoS_r17__Type SL_DRX_GC_BC_QoS_r17__cond :=
 proj2_format SL_DRX_GC_BC_QoS_r17__cond SL_DRX_GC_BC_QoS_r17__list_format  SL_DRX_GC_BC_QoS_r17__F1 SL_DRX_GC_BC_QoS_r17__F2 SL_DRX_GC_BC_QoS_r17__helper1 SL_DRX_GC_BC_QoS_r17__helper2 SL_DRX_GC_BC_QoS_r17__helper3.

Opaque SL_DRX_GC_BC_QoS_r17__cond SL_DRX_GC_BC_QoS_r17__Format.

