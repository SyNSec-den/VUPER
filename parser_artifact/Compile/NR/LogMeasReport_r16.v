Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.AbsoluteTimeInfo_r16.

Opaque AbsoluteTimeInfo_r16__cond AbsoluteTimeInfo_r16__Format.

Require Import NR.TraceReference_r16.

Opaque TraceReference_r16__cond TraceReference_r16__Format.

Definition LogMeasReport_r16__traceRecordingSessionRef_r16__Type := octet_string.
Definition LogMeasReport_r16__traceRecordingSessionRef_r16__cond := (fun bs : octet_string => (Z.of_nat (length bs) = 2)%Z).
Definition LogMeasReport_r16__tce_Id_r16__Type := octet_string.
Definition LogMeasReport_r16__tce_Id_r16__cond := (fun bs : octet_string => (Z.of_nat (length bs) = 1)%Z).
Require Import NR.LogMeasInfoList_r16.

Opaque LogMeasInfoList_r16__cond LogMeasInfoList_r16__Format.

Inductive LogMeasReport_r16__logMeasAvailable_r16__Type : Set :=
 | LogMeasReport_r16__logMeasAvailable_r16__true
.
Definition LogMeasReport_r16__logMeasAvailable_r16__cond := (fun (_ : LogMeasReport_r16__logMeasAvailable_r16__Type) => True).
Lemma LogMeasReport_r16__logMeasAvailable_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogMeasReport_r16__logMeasAvailable_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LogMeasReport_r16__logMeasAvailable_r16__nat__helper.

Definition LogMeasReport_r16__logMeasAvailable_r16__F1 t :=
  match t with
  | LogMeasReport_r16__logMeasAvailable_r16__true => 0
  end.
Definition LogMeasReport_r16__logMeasAvailable_r16__F2 n :=
  match n with
  | 0 => LogMeasReport_r16__logMeasAvailable_r16__true
  | _ => LogMeasReport_r16__logMeasAvailable_r16__true
  end.
Lemma LogMeasReport_r16__logMeasAvailable_r16__F1F2 : forall x : LogMeasReport_r16__logMeasAvailable_r16__Type, (LogMeasReport_r16__logMeasAvailable_r16__F1 x <= 0) /\ LogMeasReport_r16__logMeasAvailable_r16__F2 (LogMeasReport_r16__logMeasAvailable_r16__F1 x) = x. imp_solve. Qed.
Lemma LogMeasReport_r16__logMeasAvailable_r16__F2F1 : forall (y : nat) (H : y <= 0), LogMeasReport_r16__logMeasAvailable_r16__F1 (LogMeasReport_r16__logMeasAvailable_r16__F2 y) = y. enum_solve H y. Qed.

Inductive LogMeasReport_r16__logMeasAvailableBT_r16__Type : Set :=
 | LogMeasReport_r16__logMeasAvailableBT_r16__true
.
Definition LogMeasReport_r16__logMeasAvailableBT_r16__cond := (fun (_ : LogMeasReport_r16__logMeasAvailableBT_r16__Type) => True).
Lemma LogMeasReport_r16__logMeasAvailableBT_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogMeasReport_r16__logMeasAvailableBT_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LogMeasReport_r16__logMeasAvailableBT_r16__nat__helper.

Definition LogMeasReport_r16__logMeasAvailableBT_r16__F1 t :=
  match t with
  | LogMeasReport_r16__logMeasAvailableBT_r16__true => 0
  end.
Definition LogMeasReport_r16__logMeasAvailableBT_r16__F2 n :=
  match n with
  | 0 => LogMeasReport_r16__logMeasAvailableBT_r16__true
  | _ => LogMeasReport_r16__logMeasAvailableBT_r16__true
  end.
Lemma LogMeasReport_r16__logMeasAvailableBT_r16__F1F2 : forall x : LogMeasReport_r16__logMeasAvailableBT_r16__Type, (LogMeasReport_r16__logMeasAvailableBT_r16__F1 x <= 0) /\ LogMeasReport_r16__logMeasAvailableBT_r16__F2 (LogMeasReport_r16__logMeasAvailableBT_r16__F1 x) = x. imp_solve. Qed.
Lemma LogMeasReport_r16__logMeasAvailableBT_r16__F2F1 : forall (y : nat) (H : y <= 0), LogMeasReport_r16__logMeasAvailableBT_r16__F1 (LogMeasReport_r16__logMeasAvailableBT_r16__F2 y) = y. enum_solve H y. Qed.

Inductive LogMeasReport_r16__logMeasAvailableWLAN_r16__Type : Set :=
 | LogMeasReport_r16__logMeasAvailableWLAN_r16__true
.
Definition LogMeasReport_r16__logMeasAvailableWLAN_r16__cond := (fun (_ : LogMeasReport_r16__logMeasAvailableWLAN_r16__Type) => True).
Lemma LogMeasReport_r16__logMeasAvailableWLAN_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogMeasReport_r16__logMeasAvailableWLAN_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LogMeasReport_r16__logMeasAvailableWLAN_r16__nat__helper.

Definition LogMeasReport_r16__logMeasAvailableWLAN_r16__F1 t :=
  match t with
  | LogMeasReport_r16__logMeasAvailableWLAN_r16__true => 0
  end.
Definition LogMeasReport_r16__logMeasAvailableWLAN_r16__F2 n :=
  match n with
  | 0 => LogMeasReport_r16__logMeasAvailableWLAN_r16__true
  | _ => LogMeasReport_r16__logMeasAvailableWLAN_r16__true
  end.
Lemma LogMeasReport_r16__logMeasAvailableWLAN_r16__F1F2 : forall x : LogMeasReport_r16__logMeasAvailableWLAN_r16__Type, (LogMeasReport_r16__logMeasAvailableWLAN_r16__F1 x <= 0) /\ LogMeasReport_r16__logMeasAvailableWLAN_r16__F2 (LogMeasReport_r16__logMeasAvailableWLAN_r16__F1 x) = x. imp_solve. Qed.
Lemma LogMeasReport_r16__logMeasAvailableWLAN_r16__F2F1 : forall (y : nat) (H : y <= 0), LogMeasReport_r16__logMeasAvailableWLAN_r16__F1 (LogMeasReport_r16__logMeasAvailableWLAN_r16__F2 y) = y. enum_solve H y. Qed.

Record LogMeasReport_r16__Type : Set :=
  make__LogMeasReport_r16__Type {
    LogMeasReport_r16__absoluteTimeStamp_r16 : AbsoluteTimeInfo_r16__Type ;
    LogMeasReport_r16__traceReference_r16 : TraceReference_r16__Type ;
    LogMeasReport_r16__traceRecordingSessionRef_r16 : LogMeasReport_r16__traceRecordingSessionRef_r16__Type ;
    LogMeasReport_r16__tce_Id_r16 : LogMeasReport_r16__tce_Id_r16__Type ;
    LogMeasReport_r16__logMeasInfoList_r16 : LogMeasInfoList_r16__Type ;
    LogMeasReport_r16__logMeasAvailable_r16 : option LogMeasReport_r16__logMeasAvailable_r16__Type ;
    LogMeasReport_r16__logMeasAvailableBT_r16 : option LogMeasReport_r16__logMeasAvailableBT_r16__Type ;
    LogMeasReport_r16__logMeasAvailableWLAN_r16 : option LogMeasReport_r16__logMeasAvailableWLAN_r16__Type ;
}.
Definition LogMeasReport_r16__root_list : list seq_elem := (
 Nor AbsoluteTimeInfo_r16__Type AbsoluteTimeInfo_r16__cond ::
 Nor TraceReference_r16__Type TraceReference_r16__cond ::
 Nor LogMeasReport_r16__traceRecordingSessionRef_r16__Type LogMeasReport_r16__traceRecordingSessionRef_r16__cond ::
 Nor LogMeasReport_r16__tce_Id_r16__Type LogMeasReport_r16__tce_Id_r16__cond ::
 Nor LogMeasInfoList_r16__Type LogMeasInfoList_r16__cond ::
 Opt LogMeasReport_r16__logMeasAvailable_r16__Type LogMeasReport_r16__logMeasAvailable_r16__cond ::
 Opt LogMeasReport_r16__logMeasAvailableBT_r16__Type LogMeasReport_r16__logMeasAvailableBT_r16__cond ::
 Opt LogMeasReport_r16__logMeasAvailableWLAN_r16__Type LogMeasReport_r16__logMeasAvailableWLAN_r16__cond ::
 nil).
Definition LogMeasReport_r16__ext_list : list typ := (
  nil).
Definition LogMeasReport_r16__cond (z : LogMeasReport_r16__Type) := 
(  AbsoluteTimeInfo_r16__cond (LogMeasReport_r16__absoluteTimeStamp_r16 z) /\
  TraceReference_r16__cond (LogMeasReport_r16__traceReference_r16 z) /\
  LogMeasReport_r16__traceRecordingSessionRef_r16__cond (LogMeasReport_r16__traceRecordingSessionRef_r16 z) /\
  LogMeasReport_r16__tce_Id_r16__cond (LogMeasReport_r16__tce_Id_r16 z) /\
  LogMeasInfoList_r16__cond (LogMeasReport_r16__logMeasInfoList_r16 z) /\
  opt_cond LogMeasReport_r16__logMeasAvailable_r16__cond (LogMeasReport_r16__logMeasAvailable_r16 z) /\
  opt_cond LogMeasReport_r16__logMeasAvailableBT_r16__cond (LogMeasReport_r16__logMeasAvailableBT_r16 z) /\
  opt_cond LogMeasReport_r16__logMeasAvailableWLAN_r16__cond (LogMeasReport_r16__logMeasAvailableWLAN_r16 z) /\
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
Definition LogMeasReport_r16__traceRecordingSessionRef_r16__Format : T_Format LogMeasReport_r16__traceRecordingSessionRef_r16__Type LogMeasReport_r16__traceRecordingSessionRef_r16__cond := (* Eval compute in *) octet_string_fixed_format 2.
Opaque LogMeasReport_r16__traceRecordingSessionRef_r16__cond LogMeasReport_r16__traceRecordingSessionRef_r16__Format.

Definition LogMeasReport_r16__tce_Id_r16__Format : T_Format LogMeasReport_r16__tce_Id_r16__Type LogMeasReport_r16__tce_Id_r16__cond := (* Eval compute in *) octet_string_fixed_format 1.
Opaque LogMeasReport_r16__tce_Id_r16__cond LogMeasReport_r16__tce_Id_r16__Format.

Definition LogMeasReport_r16__logMeasAvailable_r16__Format : T_Format LogMeasReport_r16__logMeasAvailable_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogMeasReport_r16__logMeasAvailable_r16__nat__Format LogMeasReport_r16__logMeasAvailable_r16__F1 LogMeasReport_r16__logMeasAvailable_r16__F2 LogMeasReport_r16__logMeasAvailable_r16__F1F2 LogMeasReport_r16__logMeasAvailable_r16__F2F1.

Opaque LogMeasReport_r16__logMeasAvailable_r16__cond LogMeasReport_r16__logMeasAvailable_r16__Format.

Definition LogMeasReport_r16__logMeasAvailableBT_r16__Format : T_Format LogMeasReport_r16__logMeasAvailableBT_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogMeasReport_r16__logMeasAvailableBT_r16__nat__Format LogMeasReport_r16__logMeasAvailableBT_r16__F1 LogMeasReport_r16__logMeasAvailableBT_r16__F2 LogMeasReport_r16__logMeasAvailableBT_r16__F1F2 LogMeasReport_r16__logMeasAvailableBT_r16__F2F1.

Opaque LogMeasReport_r16__logMeasAvailableBT_r16__cond LogMeasReport_r16__logMeasAvailableBT_r16__Format.

Definition LogMeasReport_r16__logMeasAvailableWLAN_r16__Format : T_Format LogMeasReport_r16__logMeasAvailableWLAN_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogMeasReport_r16__logMeasAvailableWLAN_r16__nat__Format LogMeasReport_r16__logMeasAvailableWLAN_r16__F1 LogMeasReport_r16__logMeasAvailableWLAN_r16__F2 LogMeasReport_r16__logMeasAvailableWLAN_r16__F1F2 LogMeasReport_r16__logMeasAvailableWLAN_r16__F2F1.

Opaque LogMeasReport_r16__logMeasAvailableWLAN_r16__cond LogMeasReport_r16__logMeasAvailableWLAN_r16__Format.


Definition LogMeasReport_r16__root_Format_Type := Eval cbn in seq_format_prod LogMeasReport_r16__root_list.
Definition LogMeasReport_r16__root_Format_list : LogMeasReport_r16__root_Format_Type :=
  (AbsoluteTimeInfo_r16__Format, (TraceReference_r16__Format, (LogMeasReport_r16__traceRecordingSessionRef_r16__Format, (LogMeasReport_r16__tce_Id_r16__Format, (LogMeasInfoList_r16__Format, (LogMeasReport_r16__logMeasAvailable_r16__Format, (LogMeasReport_r16__logMeasAvailableBT_r16__Format, (LogMeasReport_r16__logMeasAvailableWLAN_r16__Format, unit_format)))))))).

Definition LogMeasReport_r16__ext_Format_Type := Eval cbn in get_formats LogMeasReport_r16__ext_list.
Definition LogMeasReport_r16__ext_Format_list : LogMeasReport_r16__ext_Format_Type :=
  unit__Format.

Definition LogMeasReport_r16__list_type : Set := (seq_type LogMeasReport_r16__root_list) * (seq_ext_type LogMeasReport_r16__ext_list).
Definition LogMeasReport_r16__list_cond (z : LogMeasReport_r16__list_type) : Prop :=
        (seq_cond LogMeasReport_r16__root_list (fst z)) /\ (seq_ext_cond LogMeasReport_r16__ext_list (snd z)).
Definition LogMeasReport_r16__list_format : T_Format LogMeasReport_r16__list_type LogMeasReport_r16__list_cond :=
 (* Eval compute in *) seq_ext_format LogMeasReport_r16__root_list LogMeasReport_r16__root_Format_list LogMeasReport_r16__ext_list LogMeasReport_r16__ext_Format_list.

Opaque LogMeasReport_r16__list_format.
Definition LogMeasReport_r16__F1 (z : LogMeasReport_r16__Type) : LogMeasReport_r16__list_type :=
  (((LogMeasReport_r16__absoluteTimeStamp_r16 z, (LogMeasReport_r16__traceReference_r16 z, (LogMeasReport_r16__traceRecordingSessionRef_r16 z, (LogMeasReport_r16__tce_Id_r16 z, (LogMeasReport_r16__logMeasInfoList_r16 z, (LogMeasReport_r16__logMeasAvailable_r16 z, (LogMeasReport_r16__logMeasAvailableBT_r16 z, (LogMeasReport_r16__logMeasAvailableWLAN_r16 z, tt))))))))), (
tt)).
Definition LogMeasReport_r16__F2 (y : LogMeasReport_r16__list_type) : LogMeasReport_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), _)=>
    make__LogMeasReport_r16__Type j0 j1 j2 j3 j4 j5 j6 j7
  end.
Definition LogMeasReport_r16__helper1 : (forall a : LogMeasReport_r16__Type, LogMeasReport_r16__cond a -> LogMeasReport_r16__list_cond (LogMeasReport_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition LogMeasReport_r16__helper2 : (forall a : LogMeasReport_r16__Type, LogMeasReport_r16__F2 (LogMeasReport_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition LogMeasReport_r16__helper3 : (forall b : LogMeasReport_r16__list_type, LogMeasReport_r16__list_cond b -> LogMeasReport_r16__cond (LogMeasReport_r16__F2 b) /\ LogMeasReport_r16__F1 (LogMeasReport_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold LogMeasReport_r16__cond, LogMeasReport_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition LogMeasReport_r16__Format : T_Format LogMeasReport_r16__Type LogMeasReport_r16__cond :=
 proj2_format LogMeasReport_r16__cond LogMeasReport_r16__list_format  LogMeasReport_r16__F1 LogMeasReport_r16__F2 LogMeasReport_r16__helper1 LogMeasReport_r16__helper2 LogMeasReport_r16__helper3.

Opaque LogMeasReport_r16__cond LogMeasReport_r16__Format.

