Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Type : Set :=
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl0
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl1
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl2
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl4
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare4
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare3
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare2
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare1
.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__cond := (fun (_ : SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Type) => True).
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__nat__helper.

Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F1 t :=
  match t with
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl0 => 0
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl1 => 1
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl2 => 2
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl4 => 3
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare4 => 4
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare3 => 5
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare2 => 6
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare1 => 7
  end.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F2 n :=
  match n with
  | 0 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl0
  | 1 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl1
  | 2 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl2
  | 3 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl4
  | 4 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare4
  | 5 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare3
  | 6 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare2
  | 7 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__spare1
  | _ => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__sl0
  end.
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F1F2 : forall x : SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Type, (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F1 x <= 7) /\ SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F2 (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F2F1 : forall (y : nat) (H : y <= 7), SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F1 (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Type : Set :=
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl0
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl1
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl2
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl4
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare4
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare3
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare2
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare1
.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__cond := (fun (_ : SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Type) => True).
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__nat__helper.

Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F1 t :=
  match t with
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl0 => 0
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl1 => 1
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl2 => 2
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl4 => 3
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare4 => 4
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare3 => 5
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare2 => 6
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare1 => 7
  end.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F2 n :=
  match n with
  | 0 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl0
  | 1 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl1
  | 2 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl2
  | 3 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl4
  | 4 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare4
  | 5 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare3
  | 6 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare2
  | 7 => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__spare1
  | _ => SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__sl0
  end.
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F1F2 : forall x : SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Type, (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F1 x <= 7) /\ SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F2 (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F2F1 : forall (y : nat) (H : y <= 7), SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F1 (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Type : Set :=
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl0
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl1
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl2
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl4
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl6
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl8
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl16
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl24
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl33
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl40
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl64
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl80
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl96
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl112
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl128
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl160
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl320
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare15
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare14
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare13
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare12
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare11
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare10
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare9
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare8
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare7
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare6
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare5
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare4
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare3
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare2
 | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare1
.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__cond := (fun (_ : SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Type) => True).
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__nat__helper : to_bit_sz 31 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__nat__Format : T_Format nat (fun z => (z <= 31)) :=
  nat_enum_format 31 SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__nat__helper.

Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F1 t :=
  match t with
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl0 => 0
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl1 => 1
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl2 => 2
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl4 => 3
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl6 => 4
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl8 => 5
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl16 => 6
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl24 => 7
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl33 => 8
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl40 => 9
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl64 => 10
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl80 => 11
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl96 => 12
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl112 => 13
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl128 => 14
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl160 => 15
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl320 => 16
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare15 => 17
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare14 => 18
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare13 => 19
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare12 => 20
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare11 => 21
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare10 => 22
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare9 => 23
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare8 => 24
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare7 => 25
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare6 => 26
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare5 => 27
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare4 => 28
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare3 => 29
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare2 => 30
  | SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare1 => 31
  end.
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F2 n :=
  match n with
  | 0 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl0
  | 1 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl1
  | 2 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl2
  | 3 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl4
  | 4 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl6
  | 5 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl8
  | 6 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl16
  | 7 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl24
  | 8 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl33
  | 9 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl40
  | 10 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl64
  | 11 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl80
  | 12 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl96
  | 13 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl112
  | 14 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl128
  | 15 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl160
  | 16 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl320
  | 17 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare15
  | 18 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare14
  | 19 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare13
  | 20 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare12
  | 21 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare11
  | 22 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare10
  | 23 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare9
  | 24 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare8
  | 25 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare7
  | 26 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare6
  | 27 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare5
  | 28 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare4
  | 29 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare3
  | 30 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare2
  | 31 => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__spare1
  | _ => SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__sl0
  end.
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F1F2 : forall x : SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Type, (SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F1 x <= 31) /\ SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F2 (SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F2F1 : forall (y : nat) (H : y <= 31), SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F1 (SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F2 y) = y. enum_solve H y. Qed.

Record SL_DRX_GC_Generic_r17__Type : Set :=
  make__SL_DRX_GC_Generic_r17__Type {
    SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17 : option SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Type ;
    SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17 : option SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Type ;
    SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17 : SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Type ;
}.
Definition SL_DRX_GC_Generic_r17__list := (
 Opt SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Type SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__cond ::
 Opt SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Type SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__cond ::
 Nor SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Type SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__cond ::
 nil).
Definition SL_DRX_GC_Generic_r17__cond z := 
  opt_cond SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__cond (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17 z) /\
  opt_cond SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__cond (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17 z) /\
  SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__cond (SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17 z) /\
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
Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Format : T_Format SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__nat__Format SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F1 SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F2 SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F1F2 SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__F2F1.

Opaque SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__cond SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Format.

Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Format : T_Format SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__nat__Format SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F1 SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F2 SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F1F2 SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__F2F1.

Opaque SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__cond SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Format.

Definition SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Format : T_Format SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__nat__Format SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F1 SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F2 SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F1F2 SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__F2F1.

Opaque SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__cond SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Format.


Definition SL_DRX_GC_Generic_r17__Format_Type := Eval cbn in seq_format_prod SL_DRX_GC_Generic_r17__list.
Definition SL_DRX_GC_Generic_r17__Format_list : SL_DRX_GC_Generic_r17__Format_Type :=
  (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17__Format, (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17__Format, (SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17__Format, unit_format))).
Definition SL_DRX_GC_Generic_r17__list__Format := (*Eval compute in *) seq_format SL_DRX_GC_Generic_r17__list SL_DRX_GC_Generic_r17__Format_list.
Definition SL_DRX_GC_Generic_r17__F1 z :=
  (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer1_r17 z, (SL_DRX_GC_Generic_r17__sl_DRX_GC_HARQ_RTT_Timer2_r17 z, (SL_DRX_GC_Generic_r17__sl_DRX_GC_RetransmissionTimer_r17 z, tt))).
Definition SL_DRX_GC_Generic_r17__F2 (y : seq_type SL_DRX_GC_Generic_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SL_DRX_GC_Generic_r17__Type i0 i1 i2
  end.
Lemma SL_DRX_GC_Generic_r17__F1F2_cond (z : SL_DRX_GC_Generic_r17__Type)
  : SL_DRX_GC_Generic_r17__cond z ->
  (seq_cond SL_DRX_GC_Generic_r17__list (SL_DRX_GC_Generic_r17__F1 z)).
intro H. unfold SL_DRX_GC_Generic_r17__cond in H. simpl. auto. Qed.
Lemma SL_DRX_GC_Generic_r17__F1F2_cond2 (z : SL_DRX_GC_Generic_r17__Type)
 : SL_DRX_GC_Generic_r17__F2 (SL_DRX_GC_Generic_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_DRX_GC_Generic_r17__F2F1_cond (y : seq_type SL_DRX_GC_Generic_r17__list)
  : seq_cond SL_DRX_GC_Generic_r17__list y ->
 (SL_DRX_GC_Generic_r17__cond (SL_DRX_GC_Generic_r17__F2 y)) /\  SL_DRX_GC_Generic_r17__F1 (SL_DRX_GC_Generic_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_DRX_GC_Generic_r17__cond. simpl in *. auto.
 - simpl. unfold SL_DRX_GC_Generic_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_DRX_GC_Generic_r17__Format : T_Format SL_DRX_GC_Generic_r17__Type SL_DRX_GC_Generic_r17__cond :=
        proj2_format  SL_DRX_GC_Generic_r17__cond SL_DRX_GC_Generic_r17__list__Format
    SL_DRX_GC_Generic_r17__F1 SL_DRX_GC_Generic_r17__F2 SL_DRX_GC_Generic_r17__F1F2_cond  SL_DRX_GC_Generic_r17__F1F2_cond2 SL_DRX_GC_Generic_r17__F2F1_cond.
Opaque SL_DRX_GC_Generic_r17__cond SL_DRX_GC_Generic_r17__Format.

