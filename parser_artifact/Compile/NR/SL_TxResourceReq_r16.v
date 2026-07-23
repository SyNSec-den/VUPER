Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_DestinationIdentity_r16.

Opaque SL_DestinationIdentity_r16__cond SL_DestinationIdentity_r16__Format.

Inductive SL_TxResourceReq_r16__sl_CastType_r16__Type : Set :=
 | SL_TxResourceReq_r16__sl_CastType_r16__broadcast
 | SL_TxResourceReq_r16__sl_CastType_r16__groupcast
 | SL_TxResourceReq_r16__sl_CastType_r16__unicast
 | SL_TxResourceReq_r16__sl_CastType_r16__spare1
.
Definition SL_TxResourceReq_r16__sl_CastType_r16__cond := (fun (_ : SL_TxResourceReq_r16__sl_CastType_r16__Type) => True).
Lemma SL_TxResourceReq_r16__sl_CastType_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_TxResourceReq_r16__sl_CastType_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SL_TxResourceReq_r16__sl_CastType_r16__nat__helper.

Definition SL_TxResourceReq_r16__sl_CastType_r16__F1 t :=
  match t with
  | SL_TxResourceReq_r16__sl_CastType_r16__broadcast => 0
  | SL_TxResourceReq_r16__sl_CastType_r16__groupcast => 1
  | SL_TxResourceReq_r16__sl_CastType_r16__unicast => 2
  | SL_TxResourceReq_r16__sl_CastType_r16__spare1 => 3
  end.
Definition SL_TxResourceReq_r16__sl_CastType_r16__F2 n :=
  match n with
  | 0 => SL_TxResourceReq_r16__sl_CastType_r16__broadcast
  | 1 => SL_TxResourceReq_r16__sl_CastType_r16__groupcast
  | 2 => SL_TxResourceReq_r16__sl_CastType_r16__unicast
  | 3 => SL_TxResourceReq_r16__sl_CastType_r16__spare1
  | _ => SL_TxResourceReq_r16__sl_CastType_r16__broadcast
  end.
Lemma SL_TxResourceReq_r16__sl_CastType_r16__F1F2 : forall x : SL_TxResourceReq_r16__sl_CastType_r16__Type, (SL_TxResourceReq_r16__sl_CastType_r16__F1 x <= 3) /\ SL_TxResourceReq_r16__sl_CastType_r16__F2 (SL_TxResourceReq_r16__sl_CastType_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_TxResourceReq_r16__sl_CastType_r16__F2F1 : forall (y : nat) (H : y <= 3), SL_TxResourceReq_r16__sl_CastType_r16__F1 (SL_TxResourceReq_r16__sl_CastType_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_RLC_ModeIndication_r16.

Opaque SL_RLC_ModeIndication_r16__cond SL_RLC_ModeIndication_r16__Format.

Definition SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type := list SL_RLC_ModeIndication_r16__Type.

Lemma SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__helper1 : (0 <= 1 <= maxNrofSLRB_r16)%Z. unfold maxNrofSLRB_r16.
 lia. Qed.
Lemma SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSLRB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSLRB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__cond (z : SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSLRB_r16)%Z /\ (list_and SL_RLC_ModeIndication_r16__cond z) .

Require Import NR.SL_QoS_Info_r16.

Opaque SL_QoS_Info_r16__cond SL_QoS_Info_r16__Format.

Definition SL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type := list SL_QoS_Info_r16__Type.

Lemma SL_TxResourceReq_r16__sl_QoS_InfoList_r16__helper1 : (0 <= 1 <= maxNrofSL_QFIsPerDest_r16)%Z. unfold maxNrofSL_QFIsPerDest_r16.
 lia. Qed.
Lemma SL_TxResourceReq_r16__sl_QoS_InfoList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSL_QFIsPerDest_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSL_QFIsPerDest_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_TxResourceReq_r16__sl_QoS_InfoList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_TxResourceReq_r16__sl_QoS_InfoList_r16__cond (z : SL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSL_QFIsPerDest_r16)%Z /\ (list_and SL_QoS_Info_r16__cond z) .

Require Import NR.SL_TypeTxSync_r16.

Opaque SL_TypeTxSync_r16__cond SL_TypeTxSync_r16__Format.

Definition SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type := list SL_TypeTxSync_r16__Type.

Lemma SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__helper1 : (0 <= 1 <= maxNrofFreqSL_r16)%Z. unfold maxNrofFreqSL_r16.
 lia. Qed.
Lemma SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofFreqSL_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofFreqSL_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__cond (z : SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofFreqSL_r16)%Z /\ (list_and SL_TypeTxSync_r16__cond z) .

Require Import NR.SL_TxInterestedFreqList_r16.

Opaque SL_TxInterestedFreqList_r16__cond SL_TxInterestedFreqList_r16__Format.

Record SL_TxResourceReq_r16__Type : Set :=
  make__SL_TxResourceReq_r16__Type {
    SL_TxResourceReq_r16__sl_DestinationIdentity_r16 : SL_DestinationIdentity_r16__Type ;
    SL_TxResourceReq_r16__sl_CastType_r16 : SL_TxResourceReq_r16__sl_CastType_r16__Type ;
    SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16 : option SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type ;
    SL_TxResourceReq_r16__sl_QoS_InfoList_r16 : option SL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type ;
    SL_TxResourceReq_r16__sl_TypeTxSyncList_r16 : option SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type ;
    SL_TxResourceReq_r16__sl_TxInterestedFreqList_r16 : option SL_TxInterestedFreqList_r16__Type ;
    SL_TxResourceReq_r16__sl_CapabilityInformationSidelink_r16 : option octet_string ;
}.
Definition SL_TxResourceReq_r16__list := (
 Nor SL_DestinationIdentity_r16__Type SL_DestinationIdentity_r16__cond ::
 Nor SL_TxResourceReq_r16__sl_CastType_r16__Type SL_TxResourceReq_r16__sl_CastType_r16__cond ::
 Opt SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__cond ::
 Opt SL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type SL_TxResourceReq_r16__sl_QoS_InfoList_r16__cond ::
 Opt SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__cond ::
 Opt SL_TxInterestedFreqList_r16__Type SL_TxInterestedFreqList_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SL_TxResourceReq_r16__cond z := 
  SL_DestinationIdentity_r16__cond (SL_TxResourceReq_r16__sl_DestinationIdentity_r16 z) /\
  SL_TxResourceReq_r16__sl_CastType_r16__cond (SL_TxResourceReq_r16__sl_CastType_r16 z) /\
  opt_cond SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__cond (SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16 z) /\
  opt_cond SL_TxResourceReq_r16__sl_QoS_InfoList_r16__cond (SL_TxResourceReq_r16__sl_QoS_InfoList_r16 z) /\
  opt_cond SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__cond (SL_TxResourceReq_r16__sl_TypeTxSyncList_r16 z) /\
  opt_cond SL_TxInterestedFreqList_r16__cond (SL_TxResourceReq_r16__sl_TxInterestedFreqList_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SL_TxResourceReq_r16__sl_CapabilityInformationSidelink_r16 z) /\
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
Definition SL_TxResourceReq_r16__sl_CastType_r16__Format : T_Format SL_TxResourceReq_r16__sl_CastType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_TxResourceReq_r16__sl_CastType_r16__nat__Format SL_TxResourceReq_r16__sl_CastType_r16__F1 SL_TxResourceReq_r16__sl_CastType_r16__F2 SL_TxResourceReq_r16__sl_CastType_r16__F1F2 SL_TxResourceReq_r16__sl_CastType_r16__F2F1.

Opaque SL_TxResourceReq_r16__sl_CastType_r16__cond SL_TxResourceReq_r16__sl_CastType_r16__Format.

Definition SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Format : T_Format SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Type SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__cond := seq_of_format SL_RLC_ModeIndication_r16__Format 1 maxNrofSLRB_r16 SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__helper1 SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__helper2.

Opaque SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__cond SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Format.

Definition SL_TxResourceReq_r16__sl_QoS_InfoList_r16__Format : T_Format SL_TxResourceReq_r16__sl_QoS_InfoList_r16__Type SL_TxResourceReq_r16__sl_QoS_InfoList_r16__cond := seq_of_format SL_QoS_Info_r16__Format 1 maxNrofSL_QFIsPerDest_r16 SL_TxResourceReq_r16__sl_QoS_InfoList_r16__helper1 SL_TxResourceReq_r16__sl_QoS_InfoList_r16__helper2.

Opaque SL_TxResourceReq_r16__sl_QoS_InfoList_r16__cond SL_TxResourceReq_r16__sl_QoS_InfoList_r16__Format.

Definition SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Format : T_Format SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Type SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__cond := seq_of_format SL_TypeTxSync_r16__Format 1 maxNrofFreqSL_r16 SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__helper1 SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__helper2.

Opaque SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__cond SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Format.


Definition SL_TxResourceReq_r16__Format_Type := Eval cbn in seq_format_prod SL_TxResourceReq_r16__list.
Definition SL_TxResourceReq_r16__Format_list : SL_TxResourceReq_r16__Format_Type :=
  (SL_DestinationIdentity_r16__Format, (SL_TxResourceReq_r16__sl_CastType_r16__Format, (SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16__Format, (SL_TxResourceReq_r16__sl_QoS_InfoList_r16__Format, (SL_TxResourceReq_r16__sl_TypeTxSyncList_r16__Format, (SL_TxInterestedFreqList_r16__Format, (octet_string_nc__Format, unit_format))))))).
Definition SL_TxResourceReq_r16__list__Format := (*Eval compute in *) seq_format SL_TxResourceReq_r16__list SL_TxResourceReq_r16__Format_list.
Definition SL_TxResourceReq_r16__F1 z :=
  (SL_TxResourceReq_r16__sl_DestinationIdentity_r16 z, (SL_TxResourceReq_r16__sl_CastType_r16 z, (SL_TxResourceReq_r16__sl_RLC_ModeIndicationList_r16 z, (SL_TxResourceReq_r16__sl_QoS_InfoList_r16 z, (SL_TxResourceReq_r16__sl_TypeTxSyncList_r16 z, (SL_TxResourceReq_r16__sl_TxInterestedFreqList_r16 z, (SL_TxResourceReq_r16__sl_CapabilityInformationSidelink_r16 z, tt))))))).
Definition SL_TxResourceReq_r16__F2 (y : seq_type SL_TxResourceReq_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__SL_TxResourceReq_r16__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma SL_TxResourceReq_r16__F1F2_cond (z : SL_TxResourceReq_r16__Type)
  : SL_TxResourceReq_r16__cond z ->
  (seq_cond SL_TxResourceReq_r16__list (SL_TxResourceReq_r16__F1 z)).
intro H. unfold SL_TxResourceReq_r16__cond in H. simpl. auto. Qed.
Lemma SL_TxResourceReq_r16__F1F2_cond2 (z : SL_TxResourceReq_r16__Type)
 : SL_TxResourceReq_r16__F2 (SL_TxResourceReq_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_TxResourceReq_r16__F2F1_cond (y : seq_type SL_TxResourceReq_r16__list)
  : seq_cond SL_TxResourceReq_r16__list y ->
 (SL_TxResourceReq_r16__cond (SL_TxResourceReq_r16__F2 y)) /\  SL_TxResourceReq_r16__F1 (SL_TxResourceReq_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_TxResourceReq_r16__cond. simpl in *. auto.
 - simpl. unfold SL_TxResourceReq_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_TxResourceReq_r16__Format : T_Format SL_TxResourceReq_r16__Type SL_TxResourceReq_r16__cond :=
        proj2_format  SL_TxResourceReq_r16__cond SL_TxResourceReq_r16__list__Format
    SL_TxResourceReq_r16__F1 SL_TxResourceReq_r16__F2 SL_TxResourceReq_r16__F1F2_cond  SL_TxResourceReq_r16__F1F2_cond2 SL_TxResourceReq_r16__F2F1_cond.
Opaque SL_TxResourceReq_r16__cond SL_TxResourceReq_r16__Format.

