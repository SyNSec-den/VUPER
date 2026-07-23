Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Type : Set :=
 | UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__true
.
Definition UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__cond := (fun (_ : UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Type) => True).
Lemma UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__nat__helper.

Definition UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F1 t :=
  match t with
  | UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__true => 0
  end.
Definition UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F2 n :=
  match n with
  | 0 => UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__true
  | _ => UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__true
  end.
Lemma UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F1F2 : forall x : UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Type, (UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F1 x <= 0) /\ UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F2 (UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F1 x) = x. imp_solve. Qed.
Lemma UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F2F1 : forall (y : nat) (H : y <= 0), UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F1 (UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Type : Set :=
 | UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__true
.
Definition UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__cond := (fun (_ : UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Type) => True).
Lemma UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__nat__helper.

Definition UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F1 t :=
  match t with
  | UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__true => 0
  end.
Definition UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F2 n :=
  match n with
  | 0 => UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__true
  | _ => UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__true
  end.
Lemma UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F1F2 : forall x : UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Type, (UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F1 x <= 0) /\ UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F2 (UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F1 x) = x. imp_solve. Qed.
Lemma UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F2F1 : forall (y : nat) (H : y <= 0), UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F1 (UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F2 y) = y. enum_solve H y. Qed.

Record UEInformationRequest_v1700_IEs__nonCriticalExtension__Type : Set := make__UEInformationRequest_v1700_IEs__nonCriticalExtension__Type {}.
Definition UEInformationRequest_v1700_IEs__nonCriticalExtension__cond (z : UEInformationRequest_v1700_IEs__nonCriticalExtension__Type) := True.
Record UEInformationRequest_v1700_IEs__Type : Set :=
  make__UEInformationRequest_v1700_IEs__Type {
    UEInformationRequest_v1700_IEs__successHO_ReportReq_r17 : option UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Type ;
    UEInformationRequest_v1700_IEs__coarseLocationRequest_r17 : option UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Type ;
    UEInformationRequest_v1700_IEs__nonCriticalExtension : option UEInformationRequest_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition UEInformationRequest_v1700_IEs__list := (
 Opt UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Type UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__cond ::
 Opt UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Type UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__cond ::
 Opt UEInformationRequest_v1700_IEs__nonCriticalExtension__Type UEInformationRequest_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition UEInformationRequest_v1700_IEs__cond z := 
  opt_cond UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__cond (UEInformationRequest_v1700_IEs__successHO_ReportReq_r17 z) /\
  opt_cond UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__cond (UEInformationRequest_v1700_IEs__coarseLocationRequest_r17 z) /\
  opt_cond UEInformationRequest_v1700_IEs__nonCriticalExtension__cond (UEInformationRequest_v1700_IEs__nonCriticalExtension z) /\
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
Definition UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Format : T_Format UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__nat__Format UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F1 UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F2 UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F1F2 UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__F2F1.

Opaque UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__cond UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Format.

Definition UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Format : T_Format UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__nat__Format UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F1 UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F2 UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F1F2 UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__F2F1.

Opaque UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__cond UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Format.

Definition UEInformationRequest_v1700_IEs__nonCriticalExtension__helper : forall a : UEInformationRequest_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__UEInformationRequest_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UEInformationRequest_v1700_IEs__nonCriticalExtension__Format : T_Format UEInformationRequest_v1700_IEs__nonCriticalExtension__Type UEInformationRequest_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UEInformationRequest_v1700_IEs__nonCriticalExtension__Type)
    UEInformationRequest_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque UEInformationRequest_v1700_IEs__nonCriticalExtension__cond UEInformationRequest_v1700_IEs__nonCriticalExtension__Format.


Definition UEInformationRequest_v1700_IEs__Format_Type := Eval cbn in seq_format_prod UEInformationRequest_v1700_IEs__list.
Definition UEInformationRequest_v1700_IEs__Format_list : UEInformationRequest_v1700_IEs__Format_Type :=
  (UEInformationRequest_v1700_IEs__successHO_ReportReq_r17__Format, (UEInformationRequest_v1700_IEs__coarseLocationRequest_r17__Format, (UEInformationRequest_v1700_IEs__nonCriticalExtension__Format, unit_format))).
Definition UEInformationRequest_v1700_IEs__list__Format := (*Eval compute in *) seq_format UEInformationRequest_v1700_IEs__list UEInformationRequest_v1700_IEs__Format_list.
Definition UEInformationRequest_v1700_IEs__F1 z :=
  (UEInformationRequest_v1700_IEs__successHO_ReportReq_r17 z, (UEInformationRequest_v1700_IEs__coarseLocationRequest_r17 z, (UEInformationRequest_v1700_IEs__nonCriticalExtension z, tt))).
Definition UEInformationRequest_v1700_IEs__F2 (y : seq_type UEInformationRequest_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UEInformationRequest_v1700_IEs__Type i0 i1 i2
  end.
Lemma UEInformationRequest_v1700_IEs__F1F2_cond (z : UEInformationRequest_v1700_IEs__Type)
  : UEInformationRequest_v1700_IEs__cond z ->
  (seq_cond UEInformationRequest_v1700_IEs__list (UEInformationRequest_v1700_IEs__F1 z)).
intro H. unfold UEInformationRequest_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma UEInformationRequest_v1700_IEs__F1F2_cond2 (z : UEInformationRequest_v1700_IEs__Type)
 : UEInformationRequest_v1700_IEs__F2 (UEInformationRequest_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEInformationRequest_v1700_IEs__F2F1_cond (y : seq_type UEInformationRequest_v1700_IEs__list)
  : seq_cond UEInformationRequest_v1700_IEs__list y ->
 (UEInformationRequest_v1700_IEs__cond (UEInformationRequest_v1700_IEs__F2 y)) /\  UEInformationRequest_v1700_IEs__F1 (UEInformationRequest_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEInformationRequest_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold UEInformationRequest_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEInformationRequest_v1700_IEs__Format : T_Format UEInformationRequest_v1700_IEs__Type UEInformationRequest_v1700_IEs__cond :=
        proj2_format  UEInformationRequest_v1700_IEs__cond UEInformationRequest_v1700_IEs__list__Format
    UEInformationRequest_v1700_IEs__F1 UEInformationRequest_v1700_IEs__F2 UEInformationRequest_v1700_IEs__F1F2_cond  UEInformationRequest_v1700_IEs__F1F2_cond2 UEInformationRequest_v1700_IEs__F2F1_cond.
Opaque UEInformationRequest_v1700_IEs__cond UEInformationRequest_v1700_IEs__Format.

