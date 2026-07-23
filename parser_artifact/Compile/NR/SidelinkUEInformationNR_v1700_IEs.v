Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_TxResourceReqList_v1700.

Opaque SL_TxResourceReqList_v1700__cond SL_TxResourceReqList_v1700__Format.

Require Import NR.SL_RxDRX_ReportList_v1700.

Opaque SL_RxDRX_ReportList_v1700__cond SL_RxDRX_ReportList_v1700__Format.

Require Import NR.SL_RxInterestedGC_BC_DestList_r17.

Opaque SL_RxInterestedGC_BC_DestList_r17__cond SL_RxInterestedGC_BC_DestList_r17__Format.

Require Import NR.SL_InterestedFreqList_r16.

Opaque SL_InterestedFreqList_r16__cond SL_InterestedFreqList_r16__Format.

Require Import NR.SL_TxResourceReqListDisc_r17.

Opaque SL_TxResourceReqListDisc_r17__cond SL_TxResourceReqListDisc_r17__Format.

Require Import NR.SL_TxResourceReqListCommRelay_r17.

Opaque SL_TxResourceReqListCommRelay_r17__cond SL_TxResourceReqListCommRelay_r17__Format.

Inductive SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type : Set :=
 | SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__relayUE
 | SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__remoteUE
.
Definition SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__cond := (fun (_ : SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type) => True).
Lemma SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__nat__helper.

Definition SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F1 t :=
  match t with
  | SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__relayUE => 0
  | SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__remoteUE => 1
  end.
Definition SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F2 n :=
  match n with
  | 0 => SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__relayUE
  | 1 => SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__remoteUE
  | _ => SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__relayUE
  end.
Lemma SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F1F2 : forall x : SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type, (SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F1 x <= 1) /\ SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F2 (SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F1 x) = x. imp_solve. Qed.
Lemma SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F2F1 : forall (y : nat) (H : y <= 1), SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F1 (SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_SourceIdentity_r17.

Opaque SL_SourceIdentity_r17__cond SL_SourceIdentity_r17__Format.

Record SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type : Set := make__SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type {}.
Definition SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__cond (z : SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type) := True.
Record SidelinkUEInformationNR_v1700_IEs__Type : Set :=
  make__SidelinkUEInformationNR_v1700_IEs__Type {
    SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqList_v1700 : option SL_TxResourceReqList_v1700__Type ;
    SidelinkUEInformationNR_v1700_IEs__sl_RxDRX_ReportList_v1700 : option SL_RxDRX_ReportList_v1700__Type ;
    SidelinkUEInformationNR_v1700_IEs__sl_RxInterestedGC_BC_DestList_r17 : option SL_RxInterestedGC_BC_DestList_r17__Type ;
    SidelinkUEInformationNR_v1700_IEs__sl_RxInterestedFreqListDisc_r17 : option SL_InterestedFreqList_r16__Type ;
    SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqListDisc_r17 : option SL_TxResourceReqListDisc_r17__Type ;
    SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqListCommRelay_r17 : option SL_TxResourceReqListCommRelay_r17__Type ;
    SidelinkUEInformationNR_v1700_IEs__ue_Type_r17 : option SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type ;
    SidelinkUEInformationNR_v1700_IEs__sl_SourceIdentityRemoteUE_r17 : option SL_SourceIdentity_r17__Type ;
    SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension : option SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition SidelinkUEInformationNR_v1700_IEs__list := (
 Opt SL_TxResourceReqList_v1700__Type SL_TxResourceReqList_v1700__cond ::
 Opt SL_RxDRX_ReportList_v1700__Type SL_RxDRX_ReportList_v1700__cond ::
 Opt SL_RxInterestedGC_BC_DestList_r17__Type SL_RxInterestedGC_BC_DestList_r17__cond ::
 Opt SL_InterestedFreqList_r16__Type SL_InterestedFreqList_r16__cond ::
 Opt SL_TxResourceReqListDisc_r17__Type SL_TxResourceReqListDisc_r17__cond ::
 Opt SL_TxResourceReqListCommRelay_r17__Type SL_TxResourceReqListCommRelay_r17__cond ::
 Opt SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__cond ::
 Opt SL_SourceIdentity_r17__Type SL_SourceIdentity_r17__cond ::
 Opt SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition SidelinkUEInformationNR_v1700_IEs__cond z := 
  opt_cond SL_TxResourceReqList_v1700__cond (SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqList_v1700 z) /\
  opt_cond SL_RxDRX_ReportList_v1700__cond (SidelinkUEInformationNR_v1700_IEs__sl_RxDRX_ReportList_v1700 z) /\
  opt_cond SL_RxInterestedGC_BC_DestList_r17__cond (SidelinkUEInformationNR_v1700_IEs__sl_RxInterestedGC_BC_DestList_r17 z) /\
  opt_cond SL_InterestedFreqList_r16__cond (SidelinkUEInformationNR_v1700_IEs__sl_RxInterestedFreqListDisc_r17 z) /\
  opt_cond SL_TxResourceReqListDisc_r17__cond (SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqListDisc_r17 z) /\
  opt_cond SL_TxResourceReqListCommRelay_r17__cond (SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqListCommRelay_r17 z) /\
  opt_cond SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__cond (SidelinkUEInformationNR_v1700_IEs__ue_Type_r17 z) /\
  opt_cond SL_SourceIdentity_r17__cond (SidelinkUEInformationNR_v1700_IEs__sl_SourceIdentityRemoteUE_r17 z) /\
  opt_cond SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__cond (SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension z) /\
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
Definition SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Format : T_Format SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__nat__Format SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F1 SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F2 SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F1F2 SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__F2F1.

Opaque SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__cond SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Format.

Definition SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__helper : forall a : SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Format : T_Format SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Type)
    SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__cond SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Format.


Definition SidelinkUEInformationNR_v1700_IEs__Format_Type := Eval cbn in seq_format_prod SidelinkUEInformationNR_v1700_IEs__list.
Definition SidelinkUEInformationNR_v1700_IEs__Format_list : SidelinkUEInformationNR_v1700_IEs__Format_Type :=
  (SL_TxResourceReqList_v1700__Format, (SL_RxDRX_ReportList_v1700__Format, (SL_RxInterestedGC_BC_DestList_r17__Format, (SL_InterestedFreqList_r16__Format, (SL_TxResourceReqListDisc_r17__Format, (SL_TxResourceReqListCommRelay_r17__Format, (SidelinkUEInformationNR_v1700_IEs__ue_Type_r17__Format, (SL_SourceIdentity_r17__Format, (SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension__Format, unit_format))))))))).
Definition SidelinkUEInformationNR_v1700_IEs__list__Format := (*Eval compute in *) seq_format SidelinkUEInformationNR_v1700_IEs__list SidelinkUEInformationNR_v1700_IEs__Format_list.
Definition SidelinkUEInformationNR_v1700_IEs__F1 z :=
  (SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqList_v1700 z, (SidelinkUEInformationNR_v1700_IEs__sl_RxDRX_ReportList_v1700 z, (SidelinkUEInformationNR_v1700_IEs__sl_RxInterestedGC_BC_DestList_r17 z, (SidelinkUEInformationNR_v1700_IEs__sl_RxInterestedFreqListDisc_r17 z, (SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqListDisc_r17 z, (SidelinkUEInformationNR_v1700_IEs__sl_TxResourceReqListCommRelay_r17 z, (SidelinkUEInformationNR_v1700_IEs__ue_Type_r17 z, (SidelinkUEInformationNR_v1700_IEs__sl_SourceIdentityRemoteUE_r17 z, (SidelinkUEInformationNR_v1700_IEs__nonCriticalExtension z, tt))))))))).
Definition SidelinkUEInformationNR_v1700_IEs__F2 (y : seq_type SidelinkUEInformationNR_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _)))))))))=>
    make__SidelinkUEInformationNR_v1700_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Lemma SidelinkUEInformationNR_v1700_IEs__F1F2_cond (z : SidelinkUEInformationNR_v1700_IEs__Type)
  : SidelinkUEInformationNR_v1700_IEs__cond z ->
  (seq_cond SidelinkUEInformationNR_v1700_IEs__list (SidelinkUEInformationNR_v1700_IEs__F1 z)).
intro H. unfold SidelinkUEInformationNR_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma SidelinkUEInformationNR_v1700_IEs__F1F2_cond2 (z : SidelinkUEInformationNR_v1700_IEs__Type)
 : SidelinkUEInformationNR_v1700_IEs__F2 (SidelinkUEInformationNR_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SidelinkUEInformationNR_v1700_IEs__F2F1_cond (y : seq_type SidelinkUEInformationNR_v1700_IEs__list)
  : seq_cond SidelinkUEInformationNR_v1700_IEs__list y ->
 (SidelinkUEInformationNR_v1700_IEs__cond (SidelinkUEInformationNR_v1700_IEs__F2 y)) /\  SidelinkUEInformationNR_v1700_IEs__F1 (SidelinkUEInformationNR_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SidelinkUEInformationNR_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold SidelinkUEInformationNR_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SidelinkUEInformationNR_v1700_IEs__Format : T_Format SidelinkUEInformationNR_v1700_IEs__Type SidelinkUEInformationNR_v1700_IEs__cond :=
        proj2_format  SidelinkUEInformationNR_v1700_IEs__cond SidelinkUEInformationNR_v1700_IEs__list__Format
    SidelinkUEInformationNR_v1700_IEs__F1 SidelinkUEInformationNR_v1700_IEs__F2 SidelinkUEInformationNR_v1700_IEs__F1F2_cond  SidelinkUEInformationNR_v1700_IEs__F1F2_cond2 SidelinkUEInformationNR_v1700_IEs__F2F1_cond.
Opaque SidelinkUEInformationNR_v1700_IEs__cond SidelinkUEInformationNR_v1700_IEs__Format.

