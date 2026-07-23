Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.AbsoluteTimeInfo_r16.

Opaque AbsoluteTimeInfo_r16__cond AbsoluteTimeInfo_r16__Format.

Require Import NR.TraceReference_r16.

Opaque TraceReference_r16__cond TraceReference_r16__Format.

Definition VarLogMeasReport_r16__traceRecordingSessionRef_r16__Type := octet_string.
Definition VarLogMeasReport_r16__traceRecordingSessionRef_r16__cond := (fun bs : octet_string => (Z.of_nat (length bs) = 2)%Z).
Definition VarLogMeasReport_r16__tce_Id_r16__Type := octet_string.
Definition VarLogMeasReport_r16__tce_Id_r16__cond := (fun bs : octet_string => (Z.of_nat (length bs) = 1)%Z).
Require Import NR.LogMeasInfoList_r16.

Opaque LogMeasInfoList_r16__cond LogMeasInfoList_r16__Format.

Require Import NR.PLMN_IdentityList2_r16.

Opaque PLMN_IdentityList2_r16__cond PLMN_IdentityList2_r16__Format.

Inductive VarLogMeasReport_r16__sigLoggedMeasType_r17__Type : Set :=
 | VarLogMeasReport_r16__sigLoggedMeasType_r17__true
.
Definition VarLogMeasReport_r16__sigLoggedMeasType_r17__cond := (fun (_ : VarLogMeasReport_r16__sigLoggedMeasType_r17__Type) => True).
Lemma VarLogMeasReport_r16__sigLoggedMeasType_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition VarLogMeasReport_r16__sigLoggedMeasType_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 VarLogMeasReport_r16__sigLoggedMeasType_r17__nat__helper.

Definition VarLogMeasReport_r16__sigLoggedMeasType_r17__F1 t :=
  match t with
  | VarLogMeasReport_r16__sigLoggedMeasType_r17__true => 0
  end.
Definition VarLogMeasReport_r16__sigLoggedMeasType_r17__F2 n :=
  match n with
  | 0 => VarLogMeasReport_r16__sigLoggedMeasType_r17__true
  | _ => VarLogMeasReport_r16__sigLoggedMeasType_r17__true
  end.
Lemma VarLogMeasReport_r16__sigLoggedMeasType_r17__F1F2 : forall x : VarLogMeasReport_r16__sigLoggedMeasType_r17__Type, (VarLogMeasReport_r16__sigLoggedMeasType_r17__F1 x <= 0) /\ VarLogMeasReport_r16__sigLoggedMeasType_r17__F2 (VarLogMeasReport_r16__sigLoggedMeasType_r17__F1 x) = x. imp_solve. Qed.
Lemma VarLogMeasReport_r16__sigLoggedMeasType_r17__F2F1 : forall (y : nat) (H : y <= 0), VarLogMeasReport_r16__sigLoggedMeasType_r17__F1 (VarLogMeasReport_r16__sigLoggedMeasType_r17__F2 y) = y. enum_solve H y. Qed.

Record VarLogMeasReport_r16__Type : Set :=
  make__VarLogMeasReport_r16__Type {
    VarLogMeasReport_r16__absoluteTimeInfo_r16 : AbsoluteTimeInfo_r16__Type ;
    VarLogMeasReport_r16__traceReference_r16 : TraceReference_r16__Type ;
    VarLogMeasReport_r16__traceRecordingSessionRef_r16 : VarLogMeasReport_r16__traceRecordingSessionRef_r16__Type ;
    VarLogMeasReport_r16__tce_Id_r16 : VarLogMeasReport_r16__tce_Id_r16__Type ;
    VarLogMeasReport_r16__logMeasInfoList_r16 : LogMeasInfoList_r16__Type ;
    VarLogMeasReport_r16__plmn_IdentityList_r16 : PLMN_IdentityList2_r16__Type ;
    VarLogMeasReport_r16__sigLoggedMeasType_r17 : VarLogMeasReport_r16__sigLoggedMeasType_r17__Type ;
}.
Definition VarLogMeasReport_r16__list := (
 Nor AbsoluteTimeInfo_r16__Type AbsoluteTimeInfo_r16__cond ::
 Nor TraceReference_r16__Type TraceReference_r16__cond ::
 Nor VarLogMeasReport_r16__traceRecordingSessionRef_r16__Type VarLogMeasReport_r16__traceRecordingSessionRef_r16__cond ::
 Nor VarLogMeasReport_r16__tce_Id_r16__Type VarLogMeasReport_r16__tce_Id_r16__cond ::
 Nor LogMeasInfoList_r16__Type LogMeasInfoList_r16__cond ::
 Nor PLMN_IdentityList2_r16__Type PLMN_IdentityList2_r16__cond ::
 Nor VarLogMeasReport_r16__sigLoggedMeasType_r17__Type VarLogMeasReport_r16__sigLoggedMeasType_r17__cond ::
 nil).
Definition VarLogMeasReport_r16__cond z := 
  AbsoluteTimeInfo_r16__cond (VarLogMeasReport_r16__absoluteTimeInfo_r16 z) /\
  TraceReference_r16__cond (VarLogMeasReport_r16__traceReference_r16 z) /\
  VarLogMeasReport_r16__traceRecordingSessionRef_r16__cond (VarLogMeasReport_r16__traceRecordingSessionRef_r16 z) /\
  VarLogMeasReport_r16__tce_Id_r16__cond (VarLogMeasReport_r16__tce_Id_r16 z) /\
  LogMeasInfoList_r16__cond (VarLogMeasReport_r16__logMeasInfoList_r16 z) /\
  PLMN_IdentityList2_r16__cond (VarLogMeasReport_r16__plmn_IdentityList_r16 z) /\
  VarLogMeasReport_r16__sigLoggedMeasType_r17__cond (VarLogMeasReport_r16__sigLoggedMeasType_r17 z) /\
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
Definition VarLogMeasReport_r16__traceRecordingSessionRef_r16__Format : T_Format VarLogMeasReport_r16__traceRecordingSessionRef_r16__Type VarLogMeasReport_r16__traceRecordingSessionRef_r16__cond := (* Eval compute in *) octet_string_fixed_format 2.
Opaque VarLogMeasReport_r16__traceRecordingSessionRef_r16__cond VarLogMeasReport_r16__traceRecordingSessionRef_r16__Format.

Definition VarLogMeasReport_r16__tce_Id_r16__Format : T_Format VarLogMeasReport_r16__tce_Id_r16__Type VarLogMeasReport_r16__tce_Id_r16__cond := (* Eval compute in *) octet_string_fixed_format 1.
Opaque VarLogMeasReport_r16__tce_Id_r16__cond VarLogMeasReport_r16__tce_Id_r16__Format.

Definition VarLogMeasReport_r16__sigLoggedMeasType_r17__Format : T_Format VarLogMeasReport_r16__sigLoggedMeasType_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format VarLogMeasReport_r16__sigLoggedMeasType_r17__nat__Format VarLogMeasReport_r16__sigLoggedMeasType_r17__F1 VarLogMeasReport_r16__sigLoggedMeasType_r17__F2 VarLogMeasReport_r16__sigLoggedMeasType_r17__F1F2 VarLogMeasReport_r16__sigLoggedMeasType_r17__F2F1.

Opaque VarLogMeasReport_r16__sigLoggedMeasType_r17__cond VarLogMeasReport_r16__sigLoggedMeasType_r17__Format.


Definition VarLogMeasReport_r16__Format_Type := Eval cbn in seq_format_prod VarLogMeasReport_r16__list.
Definition VarLogMeasReport_r16__Format_list : VarLogMeasReport_r16__Format_Type :=
  (AbsoluteTimeInfo_r16__Format, (TraceReference_r16__Format, (VarLogMeasReport_r16__traceRecordingSessionRef_r16__Format, (VarLogMeasReport_r16__tce_Id_r16__Format, (LogMeasInfoList_r16__Format, (PLMN_IdentityList2_r16__Format, (VarLogMeasReport_r16__sigLoggedMeasType_r17__Format, unit_format))))))).
Definition VarLogMeasReport_r16__list__Format := (*Eval compute in *) seq_format VarLogMeasReport_r16__list VarLogMeasReport_r16__Format_list.
Definition VarLogMeasReport_r16__F1 z :=
  (VarLogMeasReport_r16__absoluteTimeInfo_r16 z, (VarLogMeasReport_r16__traceReference_r16 z, (VarLogMeasReport_r16__traceRecordingSessionRef_r16 z, (VarLogMeasReport_r16__tce_Id_r16 z, (VarLogMeasReport_r16__logMeasInfoList_r16 z, (VarLogMeasReport_r16__plmn_IdentityList_r16 z, (VarLogMeasReport_r16__sigLoggedMeasType_r17 z, tt))))))).
Definition VarLogMeasReport_r16__F2 (y : seq_type VarLogMeasReport_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__VarLogMeasReport_r16__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma VarLogMeasReport_r16__F1F2_cond (z : VarLogMeasReport_r16__Type)
  : VarLogMeasReport_r16__cond z ->
  (seq_cond VarLogMeasReport_r16__list (VarLogMeasReport_r16__F1 z)).
intro H. unfold VarLogMeasReport_r16__cond in H. simpl. auto. Qed.
Lemma VarLogMeasReport_r16__F1F2_cond2 (z : VarLogMeasReport_r16__Type)
 : VarLogMeasReport_r16__F2 (VarLogMeasReport_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarLogMeasReport_r16__F2F1_cond (y : seq_type VarLogMeasReport_r16__list)
  : seq_cond VarLogMeasReport_r16__list y ->
 (VarLogMeasReport_r16__cond (VarLogMeasReport_r16__F2 y)) /\  VarLogMeasReport_r16__F1 (VarLogMeasReport_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarLogMeasReport_r16__cond. simpl in *. auto.
 - simpl. unfold VarLogMeasReport_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarLogMeasReport_r16__Format : T_Format VarLogMeasReport_r16__Type VarLogMeasReport_r16__cond :=
        proj2_format  VarLogMeasReport_r16__cond VarLogMeasReport_r16__list__Format
    VarLogMeasReport_r16__F1 VarLogMeasReport_r16__F2 VarLogMeasReport_r16__F1F2_cond  VarLogMeasReport_r16__F1F2_cond2 VarLogMeasReport_r16__F2F1_cond.
Opaque VarLogMeasReport_r16__cond VarLogMeasReport_r16__Format.

