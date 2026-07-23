Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type : Set :=
 | RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__true
.
Definition RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__cond := (fun (_ : RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type) => True).
Lemma RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__nat__helper.

Definition RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F1 t :=
  match t with
  | RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__true => 0
  end.
Definition RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F2 n :=
  match n with
  | 0 => RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__true
  | _ => RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__true
  end.
Lemma RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F1F2 : forall x : RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type, (RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F1 x <= 0) /\ RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F2 (RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F1 x) = x. imp_solve. Qed.
Lemma RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F2F1 : forall (y : nat) (H : y <= 0), RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F1 (RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasResultIdleEUTRA_r16.

Opaque MeasResultIdleEUTRA_r16__cond MeasResultIdleEUTRA_r16__Format.

Require Import NR.MeasResultIdleNR_r16.

Opaque MeasResultIdleNR_r16__cond MeasResultIdleNR_r16__Format.


Inductive RRCResumeComplete_v1610_IEs__scg_Response_r16__Type : Set :=
  | RRCResumeComplete_v1610_IEs__scg_Response_r16__nr_SCG_Response : octet_string -> RRCResumeComplete_v1610_IEs__scg_Response_r16__Type
  | RRCResumeComplete_v1610_IEs__scg_Response_r16__eutra_SCG_Response : octet_string -> RRCResumeComplete_v1610_IEs__scg_Response_r16__Type
.
Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__list : list typ := (
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__cond (c : RRCResumeComplete_v1610_IEs__scg_Response_r16__Type) := 
  match c with
  | RRCResumeComplete_v1610_IEs__scg_Response_r16__nr_SCG_Response t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  | RRCResumeComplete_v1610_IEs__scg_Response_r16__eutra_SCG_Response t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  end.

Lemma RRCResumeComplete_v1610_IEs__scg_Response_r16__len_helper1 : to_bit_sz (length RRCResumeComplete_v1610_IEs__scg_Response_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCResumeComplete_v1610_IEs__scg_Response_r16__len_helper2 : 2 <= length2 RRCResumeComplete_v1610_IEs__scg_Response_r16__list.
 simpl. lia. Qed.
Require Import NR.UE_MeasurementsAvailable_r16.

Opaque UE_MeasurementsAvailable_r16__cond UE_MeasurementsAvailable_r16__Format.

Inductive RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type : Set :=
 | RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__true
.
Definition RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__cond := (fun (_ : RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type) => True).
Lemma RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__nat__helper.

Definition RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F1 t :=
  match t with
  | RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__true => 0
  end.
Definition RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F2 n :=
  match n with
  | 0 => RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__true
  | _ => RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__true
  end.
Lemma RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F1F2 : forall x : RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type, (RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F1 x <= 0) /\ RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F2 (RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F1 x) = x. imp_solve. Qed.
Lemma RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F2F1 : forall (y : nat) (H : y <= 0), RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F1 (RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RRCResumeComplete_v1610_IEs__mobilityState_r16__Type : Set :=
 | RRCResumeComplete_v1610_IEs__mobilityState_r16__normal
 | RRCResumeComplete_v1610_IEs__mobilityState_r16__medium
 | RRCResumeComplete_v1610_IEs__mobilityState_r16__high
 | RRCResumeComplete_v1610_IEs__mobilityState_r16__spare
.
Definition RRCResumeComplete_v1610_IEs__mobilityState_r16__cond := (fun (_ : RRCResumeComplete_v1610_IEs__mobilityState_r16__Type) => True).
Lemma RRCResumeComplete_v1610_IEs__mobilityState_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCResumeComplete_v1610_IEs__mobilityState_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RRCResumeComplete_v1610_IEs__mobilityState_r16__nat__helper.

Definition RRCResumeComplete_v1610_IEs__mobilityState_r16__F1 t :=
  match t with
  | RRCResumeComplete_v1610_IEs__mobilityState_r16__normal => 0
  | RRCResumeComplete_v1610_IEs__mobilityState_r16__medium => 1
  | RRCResumeComplete_v1610_IEs__mobilityState_r16__high => 2
  | RRCResumeComplete_v1610_IEs__mobilityState_r16__spare => 3
  end.
Definition RRCResumeComplete_v1610_IEs__mobilityState_r16__F2 n :=
  match n with
  | 0 => RRCResumeComplete_v1610_IEs__mobilityState_r16__normal
  | 1 => RRCResumeComplete_v1610_IEs__mobilityState_r16__medium
  | 2 => RRCResumeComplete_v1610_IEs__mobilityState_r16__high
  | 3 => RRCResumeComplete_v1610_IEs__mobilityState_r16__spare
  | _ => RRCResumeComplete_v1610_IEs__mobilityState_r16__normal
  end.
Lemma RRCResumeComplete_v1610_IEs__mobilityState_r16__F1F2 : forall x : RRCResumeComplete_v1610_IEs__mobilityState_r16__Type, (RRCResumeComplete_v1610_IEs__mobilityState_r16__F1 x <= 3) /\ RRCResumeComplete_v1610_IEs__mobilityState_r16__F2 (RRCResumeComplete_v1610_IEs__mobilityState_r16__F1 x) = x. imp_solve. Qed.
Lemma RRCResumeComplete_v1610_IEs__mobilityState_r16__F2F1 : forall (y : nat) (H : y <= 3), RRCResumeComplete_v1610_IEs__mobilityState_r16__F1 (RRCResumeComplete_v1610_IEs__mobilityState_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.NeedForGapsInfoNR_r16.

Opaque NeedForGapsInfoNR_r16__cond NeedForGapsInfoNR_r16__Format.

Require Import NR.RRCResumeComplete_v1640_IEs.

Opaque RRCResumeComplete_v1640_IEs__cond RRCResumeComplete_v1640_IEs__Format.

Record RRCResumeComplete_v1610_IEs__Type : Set :=
  make__RRCResumeComplete_v1610_IEs__Type {
    RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16 : option RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type ;
    RRCResumeComplete_v1610_IEs__measResultIdleEUTRA_r16 : option MeasResultIdleEUTRA_r16__Type ;
    RRCResumeComplete_v1610_IEs__measResultIdleNR_r16 : option MeasResultIdleNR_r16__Type ;
    RRCResumeComplete_v1610_IEs__scg_Response_r16 : option RRCResumeComplete_v1610_IEs__scg_Response_r16__Type ;
    RRCResumeComplete_v1610_IEs__ue_MeasurementsAvailable_r16 : option UE_MeasurementsAvailable_r16__Type ;
    RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16 : option RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type ;
    RRCResumeComplete_v1610_IEs__mobilityState_r16 : option RRCResumeComplete_v1610_IEs__mobilityState_r16__Type ;
    RRCResumeComplete_v1610_IEs__needForGapsInfoNR_r16 : option NeedForGapsInfoNR_r16__Type ;
    RRCResumeComplete_v1610_IEs__nonCriticalExtension : option RRCResumeComplete_v1640_IEs__Type ;
}.
Definition RRCResumeComplete_v1610_IEs__list := (
 Opt RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__cond ::
 Opt MeasResultIdleEUTRA_r16__Type MeasResultIdleEUTRA_r16__cond ::
 Opt MeasResultIdleNR_r16__Type MeasResultIdleNR_r16__cond ::
 Opt RRCResumeComplete_v1610_IEs__scg_Response_r16__Type RRCResumeComplete_v1610_IEs__scg_Response_r16__cond ::
 Opt UE_MeasurementsAvailable_r16__Type UE_MeasurementsAvailable_r16__cond ::
 Opt RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__cond ::
 Opt RRCResumeComplete_v1610_IEs__mobilityState_r16__Type RRCResumeComplete_v1610_IEs__mobilityState_r16__cond ::
 Opt NeedForGapsInfoNR_r16__Type NeedForGapsInfoNR_r16__cond ::
 Opt RRCResumeComplete_v1640_IEs__Type RRCResumeComplete_v1640_IEs__cond ::
 nil).
Definition RRCResumeComplete_v1610_IEs__cond z := 
  opt_cond RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__cond (RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16 z) /\
  opt_cond MeasResultIdleEUTRA_r16__cond (RRCResumeComplete_v1610_IEs__measResultIdleEUTRA_r16 z) /\
  opt_cond MeasResultIdleNR_r16__cond (RRCResumeComplete_v1610_IEs__measResultIdleNR_r16 z) /\
  opt_cond RRCResumeComplete_v1610_IEs__scg_Response_r16__cond (RRCResumeComplete_v1610_IEs__scg_Response_r16 z) /\
  opt_cond UE_MeasurementsAvailable_r16__cond (RRCResumeComplete_v1610_IEs__ue_MeasurementsAvailable_r16 z) /\
  opt_cond RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__cond (RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16 z) /\
  opt_cond RRCResumeComplete_v1610_IEs__mobilityState_r16__cond (RRCResumeComplete_v1610_IEs__mobilityState_r16 z) /\
  opt_cond NeedForGapsInfoNR_r16__cond (RRCResumeComplete_v1610_IEs__needForGapsInfoNR_r16 z) /\
  opt_cond RRCResumeComplete_v1640_IEs__cond (RRCResumeComplete_v1610_IEs__nonCriticalExtension z) /\
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
Definition RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Format : T_Format RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__nat__Format RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F1 RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F2 RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F1F2 RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__F2F1.

Opaque RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__cond RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Format.


Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__Format_Type := Eval cbn in get_formats RRCResumeComplete_v1610_IEs__scg_Response_r16__list.
Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__Format_list : RRCResumeComplete_v1610_IEs__scg_Response_r16__Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, unit__Format)).
Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__list__Format := Eval compute in choice_format RRCResumeComplete_v1610_IEs__scg_Response_r16__list RRCResumeComplete_v1610_IEs__scg_Response_r16__len_helper1 RRCResumeComplete_v1610_IEs__scg_Response_r16__len_helper2  RRCResumeComplete_v1610_IEs__scg_Response_r16__Format_list.
Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__F1 (z : RRCResumeComplete_v1610_IEs__scg_Response_r16__Type) : (choice RRCResumeComplete_v1610_IEs__scg_Response_r16__list) :=
  match z with
   | RRCResumeComplete_v1610_IEs__scg_Response_r16__nr_SCG_Response t => existT _ 0 t
  | RRCResumeComplete_v1610_IEs__scg_Response_r16__eutra_SCG_Response t => existT _ 1 t
  end.
Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__g := (fun n => typ_set (get_nth_typ RRCResumeComplete_v1610_IEs__scg_Response_r16__list n)).
Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__F2 (y : choice RRCResumeComplete_v1610_IEs__scg_Response_r16__list) : RRCResumeComplete_v1610_IEs__scg_Response_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCResumeComplete_v1610_IEs__scg_Response_r16__g n -> RRCResumeComplete_v1610_IEs__scg_Response_r16__Type) with
    | 0 => fun (t : octet_string) => RRCResumeComplete_v1610_IEs__scg_Response_r16__nr_SCG_Response t 
    | 1 => fun (t : octet_string) => RRCResumeComplete_v1610_IEs__scg_Response_r16__eutra_SCG_Response t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCResumeComplete_v1610_IEs__scg_Response_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCResumeComplete_v1610_IEs__scg_Response_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCResumeComplete_v1610_IEs__scg_Response_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCResumeComplete_v1610_IEs__scg_Response_r16__Type with end) n0
           end t0).

Lemma RRCResumeComplete_v1610_IEs__scg_Response_r16__helper2 :  forall (y : RRCResumeComplete_v1610_IEs__scg_Response_r16__Type), RRCResumeComplete_v1610_IEs__scg_Response_r16__cond y -> choice_cond RRCResumeComplete_v1610_IEs__scg_Response_r16__list (RRCResumeComplete_v1610_IEs__scg_Response_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCResumeComplete_v1610_IEs__scg_Response_r16__helper3 :  forall (y : RRCResumeComplete_v1610_IEs__scg_Response_r16__Type), RRCResumeComplete_v1610_IEs__scg_Response_r16__F2 (RRCResumeComplete_v1610_IEs__scg_Response_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCResumeComplete_v1610_IEs__scg_Response_r16__helper4 : (forall b : choice RRCResumeComplete_v1610_IEs__scg_Response_r16__list, choice_cond RRCResumeComplete_v1610_IEs__scg_Response_r16__list b -> RRCResumeComplete_v1610_IEs__scg_Response_r16__cond (RRCResumeComplete_v1610_IEs__scg_Response_r16__F2 b) /\ RRCResumeComplete_v1610_IEs__scg_Response_r16__F1 (RRCResumeComplete_v1610_IEs__scg_Response_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCResumeComplete_v1610_IEs__scg_Response_r16__F1 RRCResumeComplete_v1610_IEs__scg_Response_r16__F2.
Definition RRCResumeComplete_v1610_IEs__scg_Response_r16__Format : T_Format RRCResumeComplete_v1610_IEs__scg_Response_r16__Type RRCResumeComplete_v1610_IEs__scg_Response_r16__cond :=
  (* Eval compute in *) proj2_format RRCResumeComplete_v1610_IEs__scg_Response_r16__cond RRCResumeComplete_v1610_IEs__scg_Response_r16__list__Format RRCResumeComplete_v1610_IEs__scg_Response_r16__F1 RRCResumeComplete_v1610_IEs__scg_Response_r16__F2 RRCResumeComplete_v1610_IEs__scg_Response_r16__helper2 RRCResumeComplete_v1610_IEs__scg_Response_r16__helper3 RRCResumeComplete_v1610_IEs__scg_Response_r16__helper4.
Opaque RRCResumeComplete_v1610_IEs__scg_Response_r16__cond RRCResumeComplete_v1610_IEs__scg_Response_r16__Format.

Definition RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Format : T_Format RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__nat__Format RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F1 RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F2 RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F1F2 RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__F2F1.

Opaque RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__cond RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Format.

Definition RRCResumeComplete_v1610_IEs__mobilityState_r16__Format : T_Format RRCResumeComplete_v1610_IEs__mobilityState_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCResumeComplete_v1610_IEs__mobilityState_r16__nat__Format RRCResumeComplete_v1610_IEs__mobilityState_r16__F1 RRCResumeComplete_v1610_IEs__mobilityState_r16__F2 RRCResumeComplete_v1610_IEs__mobilityState_r16__F1F2 RRCResumeComplete_v1610_IEs__mobilityState_r16__F2F1.

Opaque RRCResumeComplete_v1610_IEs__mobilityState_r16__cond RRCResumeComplete_v1610_IEs__mobilityState_r16__Format.


Definition RRCResumeComplete_v1610_IEs__Format_Type := Eval cbn in seq_format_prod RRCResumeComplete_v1610_IEs__list.
Definition RRCResumeComplete_v1610_IEs__Format_list : RRCResumeComplete_v1610_IEs__Format_Type :=
  (RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16__Format, (MeasResultIdleEUTRA_r16__Format, (MeasResultIdleNR_r16__Format, (RRCResumeComplete_v1610_IEs__scg_Response_r16__Format, (UE_MeasurementsAvailable_r16__Format, (RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16__Format, (RRCResumeComplete_v1610_IEs__mobilityState_r16__Format, (NeedForGapsInfoNR_r16__Format, (RRCResumeComplete_v1640_IEs__Format, unit_format))))))))).
Definition RRCResumeComplete_v1610_IEs__list__Format := (*Eval compute in *) seq_format RRCResumeComplete_v1610_IEs__list RRCResumeComplete_v1610_IEs__Format_list.
Definition RRCResumeComplete_v1610_IEs__F1 z :=
  (RRCResumeComplete_v1610_IEs__idleMeasAvailable_r16 z, (RRCResumeComplete_v1610_IEs__measResultIdleEUTRA_r16 z, (RRCResumeComplete_v1610_IEs__measResultIdleNR_r16 z, (RRCResumeComplete_v1610_IEs__scg_Response_r16 z, (RRCResumeComplete_v1610_IEs__ue_MeasurementsAvailable_r16 z, (RRCResumeComplete_v1610_IEs__mobilityHistoryAvail_r16 z, (RRCResumeComplete_v1610_IEs__mobilityState_r16 z, (RRCResumeComplete_v1610_IEs__needForGapsInfoNR_r16 z, (RRCResumeComplete_v1610_IEs__nonCriticalExtension z, tt))))))))).
Definition RRCResumeComplete_v1610_IEs__F2 (y : seq_type RRCResumeComplete_v1610_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _)))))))))=>
    make__RRCResumeComplete_v1610_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Lemma RRCResumeComplete_v1610_IEs__F1F2_cond (z : RRCResumeComplete_v1610_IEs__Type)
  : RRCResumeComplete_v1610_IEs__cond z ->
  (seq_cond RRCResumeComplete_v1610_IEs__list (RRCResumeComplete_v1610_IEs__F1 z)).
intro H. unfold RRCResumeComplete_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma RRCResumeComplete_v1610_IEs__F1F2_cond2 (z : RRCResumeComplete_v1610_IEs__Type)
 : RRCResumeComplete_v1610_IEs__F2 (RRCResumeComplete_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCResumeComplete_v1610_IEs__F2F1_cond (y : seq_type RRCResumeComplete_v1610_IEs__list)
  : seq_cond RRCResumeComplete_v1610_IEs__list y ->
 (RRCResumeComplete_v1610_IEs__cond (RRCResumeComplete_v1610_IEs__F2 y)) /\  RRCResumeComplete_v1610_IEs__F1 (RRCResumeComplete_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCResumeComplete_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCResumeComplete_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCResumeComplete_v1610_IEs__Format : T_Format RRCResumeComplete_v1610_IEs__Type RRCResumeComplete_v1610_IEs__cond :=
        proj2_format  RRCResumeComplete_v1610_IEs__cond RRCResumeComplete_v1610_IEs__list__Format
    RRCResumeComplete_v1610_IEs__F1 RRCResumeComplete_v1610_IEs__F2 RRCResumeComplete_v1610_IEs__F1F2_cond  RRCResumeComplete_v1610_IEs__F1F2_cond2 RRCResumeComplete_v1610_IEs__F2F1_cond.
Opaque RRCResumeComplete_v1610_IEs__cond RRCResumeComplete_v1610_IEs__Format.

