Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DedicatedInfoF1c_r17.

Opaque DedicatedInfoF1c_r17__cond DedicatedInfoF1c_r17__Format.

Require Import NR.RxTxTimeDiff_r17.

Opaque RxTxTimeDiff_r17__cond RxTxTimeDiff_r17__Format.

Inductive DLInformationTransfer_v1700_IEs__ta_PDC_r17__Type : Set :=
 | DLInformationTransfer_v1700_IEs__ta_PDC_r17__activate
 | DLInformationTransfer_v1700_IEs__ta_PDC_r17__deactivate
.
Definition DLInformationTransfer_v1700_IEs__ta_PDC_r17__cond := (fun (_ : DLInformationTransfer_v1700_IEs__ta_PDC_r17__Type) => True).
Lemma DLInformationTransfer_v1700_IEs__ta_PDC_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DLInformationTransfer_v1700_IEs__ta_PDC_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 DLInformationTransfer_v1700_IEs__ta_PDC_r17__nat__helper.

Definition DLInformationTransfer_v1700_IEs__ta_PDC_r17__F1 t :=
  match t with
  | DLInformationTransfer_v1700_IEs__ta_PDC_r17__activate => 0
  | DLInformationTransfer_v1700_IEs__ta_PDC_r17__deactivate => 1
  end.
Definition DLInformationTransfer_v1700_IEs__ta_PDC_r17__F2 n :=
  match n with
  | 0 => DLInformationTransfer_v1700_IEs__ta_PDC_r17__activate
  | 1 => DLInformationTransfer_v1700_IEs__ta_PDC_r17__deactivate
  | _ => DLInformationTransfer_v1700_IEs__ta_PDC_r17__activate
  end.
Lemma DLInformationTransfer_v1700_IEs__ta_PDC_r17__F1F2 : forall x : DLInformationTransfer_v1700_IEs__ta_PDC_r17__Type, (DLInformationTransfer_v1700_IEs__ta_PDC_r17__F1 x <= 1) /\ DLInformationTransfer_v1700_IEs__ta_PDC_r17__F2 (DLInformationTransfer_v1700_IEs__ta_PDC_r17__F1 x) = x. imp_solve. Qed.
Lemma DLInformationTransfer_v1700_IEs__ta_PDC_r17__F2F1 : forall (y : nat) (H : y <= 1), DLInformationTransfer_v1700_IEs__ta_PDC_r17__F1 (DLInformationTransfer_v1700_IEs__ta_PDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Type : Set :=
 | DLInformationTransfer_v1700_IEs__sib9Fallback_r17__true
.
Definition DLInformationTransfer_v1700_IEs__sib9Fallback_r17__cond := (fun (_ : DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Type) => True).
Lemma DLInformationTransfer_v1700_IEs__sib9Fallback_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DLInformationTransfer_v1700_IEs__sib9Fallback_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DLInformationTransfer_v1700_IEs__sib9Fallback_r17__nat__helper.

Definition DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F1 t :=
  match t with
  | DLInformationTransfer_v1700_IEs__sib9Fallback_r17__true => 0
  end.
Definition DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F2 n :=
  match n with
  | 0 => DLInformationTransfer_v1700_IEs__sib9Fallback_r17__true
  | _ => DLInformationTransfer_v1700_IEs__sib9Fallback_r17__true
  end.
Lemma DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F1F2 : forall x : DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Type, (DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F1 x <= 0) /\ DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F2 (DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F1 x) = x. imp_solve. Qed.
Lemma DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F2F1 : forall (y : nat) (H : y <= 0), DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F1 (DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F2 y) = y. enum_solve H y. Qed.

Record DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type : Set := make__DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type {}.
Definition DLInformationTransfer_v1700_IEs__nonCriticalExtension__cond (z : DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type) := True.
Record DLInformationTransfer_v1700_IEs__Type : Set :=
  make__DLInformationTransfer_v1700_IEs__Type {
    DLInformationTransfer_v1700_IEs__dedicatedInfoF1c_r17 : option DedicatedInfoF1c_r17__Type ;
    DLInformationTransfer_v1700_IEs__rxTxTimeDiff_gNB_r17 : option RxTxTimeDiff_r17__Type ;
    DLInformationTransfer_v1700_IEs__ta_PDC_r17 : option DLInformationTransfer_v1700_IEs__ta_PDC_r17__Type ;
    DLInformationTransfer_v1700_IEs__sib9Fallback_r17 : option DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Type ;
    DLInformationTransfer_v1700_IEs__nonCriticalExtension : option DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition DLInformationTransfer_v1700_IEs__list := (
 Opt DedicatedInfoF1c_r17__Type DedicatedInfoF1c_r17__cond ::
 Opt RxTxTimeDiff_r17__Type RxTxTimeDiff_r17__cond ::
 Opt DLInformationTransfer_v1700_IEs__ta_PDC_r17__Type DLInformationTransfer_v1700_IEs__ta_PDC_r17__cond ::
 Opt DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Type DLInformationTransfer_v1700_IEs__sib9Fallback_r17__cond ::
 Opt DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type DLInformationTransfer_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition DLInformationTransfer_v1700_IEs__cond z := 
  opt_cond DedicatedInfoF1c_r17__cond (DLInformationTransfer_v1700_IEs__dedicatedInfoF1c_r17 z) /\
  opt_cond RxTxTimeDiff_r17__cond (DLInformationTransfer_v1700_IEs__rxTxTimeDiff_gNB_r17 z) /\
  opt_cond DLInformationTransfer_v1700_IEs__ta_PDC_r17__cond (DLInformationTransfer_v1700_IEs__ta_PDC_r17 z) /\
  opt_cond DLInformationTransfer_v1700_IEs__sib9Fallback_r17__cond (DLInformationTransfer_v1700_IEs__sib9Fallback_r17 z) /\
  opt_cond DLInformationTransfer_v1700_IEs__nonCriticalExtension__cond (DLInformationTransfer_v1700_IEs__nonCriticalExtension z) /\
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
Definition DLInformationTransfer_v1700_IEs__ta_PDC_r17__Format : T_Format DLInformationTransfer_v1700_IEs__ta_PDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DLInformationTransfer_v1700_IEs__ta_PDC_r17__nat__Format DLInformationTransfer_v1700_IEs__ta_PDC_r17__F1 DLInformationTransfer_v1700_IEs__ta_PDC_r17__F2 DLInformationTransfer_v1700_IEs__ta_PDC_r17__F1F2 DLInformationTransfer_v1700_IEs__ta_PDC_r17__F2F1.

Opaque DLInformationTransfer_v1700_IEs__ta_PDC_r17__cond DLInformationTransfer_v1700_IEs__ta_PDC_r17__Format.

Definition DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Format : T_Format DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DLInformationTransfer_v1700_IEs__sib9Fallback_r17__nat__Format DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F1 DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F2 DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F1F2 DLInformationTransfer_v1700_IEs__sib9Fallback_r17__F2F1.

Opaque DLInformationTransfer_v1700_IEs__sib9Fallback_r17__cond DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Format.

Definition DLInformationTransfer_v1700_IEs__nonCriticalExtension__helper : forall a : DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition DLInformationTransfer_v1700_IEs__nonCriticalExtension__Format : T_Format DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type DLInformationTransfer_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__DLInformationTransfer_v1700_IEs__nonCriticalExtension__Type)
    DLInformationTransfer_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque DLInformationTransfer_v1700_IEs__nonCriticalExtension__cond DLInformationTransfer_v1700_IEs__nonCriticalExtension__Format.


Definition DLInformationTransfer_v1700_IEs__Format_Type := Eval cbn in seq_format_prod DLInformationTransfer_v1700_IEs__list.
Definition DLInformationTransfer_v1700_IEs__Format_list : DLInformationTransfer_v1700_IEs__Format_Type :=
  (DedicatedInfoF1c_r17__Format, (RxTxTimeDiff_r17__Format, (DLInformationTransfer_v1700_IEs__ta_PDC_r17__Format, (DLInformationTransfer_v1700_IEs__sib9Fallback_r17__Format, (DLInformationTransfer_v1700_IEs__nonCriticalExtension__Format, unit_format))))).
Definition DLInformationTransfer_v1700_IEs__list__Format := (*Eval compute in *) seq_format DLInformationTransfer_v1700_IEs__list DLInformationTransfer_v1700_IEs__Format_list.
Definition DLInformationTransfer_v1700_IEs__F1 z :=
  (DLInformationTransfer_v1700_IEs__dedicatedInfoF1c_r17 z, (DLInformationTransfer_v1700_IEs__rxTxTimeDiff_gNB_r17 z, (DLInformationTransfer_v1700_IEs__ta_PDC_r17 z, (DLInformationTransfer_v1700_IEs__sib9Fallback_r17 z, (DLInformationTransfer_v1700_IEs__nonCriticalExtension z, tt))))).
Definition DLInformationTransfer_v1700_IEs__F2 (y : seq_type DLInformationTransfer_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__DLInformationTransfer_v1700_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma DLInformationTransfer_v1700_IEs__F1F2_cond (z : DLInformationTransfer_v1700_IEs__Type)
  : DLInformationTransfer_v1700_IEs__cond z ->
  (seq_cond DLInformationTransfer_v1700_IEs__list (DLInformationTransfer_v1700_IEs__F1 z)).
intro H. unfold DLInformationTransfer_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma DLInformationTransfer_v1700_IEs__F1F2_cond2 (z : DLInformationTransfer_v1700_IEs__Type)
 : DLInformationTransfer_v1700_IEs__F2 (DLInformationTransfer_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DLInformationTransfer_v1700_IEs__F2F1_cond (y : seq_type DLInformationTransfer_v1700_IEs__list)
  : seq_cond DLInformationTransfer_v1700_IEs__list y ->
 (DLInformationTransfer_v1700_IEs__cond (DLInformationTransfer_v1700_IEs__F2 y)) /\  DLInformationTransfer_v1700_IEs__F1 (DLInformationTransfer_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DLInformationTransfer_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold DLInformationTransfer_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DLInformationTransfer_v1700_IEs__Format : T_Format DLInformationTransfer_v1700_IEs__Type DLInformationTransfer_v1700_IEs__cond :=
        proj2_format  DLInformationTransfer_v1700_IEs__cond DLInformationTransfer_v1700_IEs__list__Format
    DLInformationTransfer_v1700_IEs__F1 DLInformationTransfer_v1700_IEs__F2 DLInformationTransfer_v1700_IEs__F1F2_cond  DLInformationTransfer_v1700_IEs__F1F2_cond2 DLInformationTransfer_v1700_IEs__F2F1_cond.
Opaque DLInformationTransfer_v1700_IEs__cond DLInformationTransfer_v1700_IEs__Format.

