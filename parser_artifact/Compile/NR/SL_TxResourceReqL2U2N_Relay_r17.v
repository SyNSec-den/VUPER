Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_DestinationIdentity_r16.

Opaque SL_DestinationIdentity_r16__cond SL_DestinationIdentity_r16__Format.

Require Import NR.SL_TxInterestedFreqList_r16.

Opaque SL_TxInterestedFreqList_r16__cond SL_TxInterestedFreqList_r16__Format.

Require Import NR.SL_TypeTxSync_r16.

Opaque SL_TypeTxSync_r16__cond SL_TypeTxSync_r16__Format.

Definition SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Type := list SL_TypeTxSync_r16__Type.

Lemma SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__helper1 : (0 <= 1 <= maxNrofFreqSL_r16)%Z. unfold maxNrofFreqSL_r16.
 lia. Qed.
Lemma SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofFreqSL_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofFreqSL_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__cond (z : SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofFreqSL_r16)%Z /\ (list_and SL_TypeTxSync_r16__cond z) .

Inductive SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type : Set :=
 | SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__true
.
Definition SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__cond := (fun (_ : SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type) => True).
Lemma SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__nat__helper.

Definition SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F1 t :=
  match t with
  | SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__true => 0
  end.
Definition SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F2 n :=
  match n with
  | 0 => SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__true
  | _ => SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__true
  end.
Lemma SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F1F2 : forall x : SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type, (SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F1 x <= 0) /\ SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F2 (SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F1 x) = x. imp_solve. Qed.
Lemma SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F2F1 : forall (y : nat) (H : y <= 0), SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F1 (SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_PagingIdentityRemoteUE_r17.

Opaque SL_PagingIdentityRemoteUE_r17__cond SL_PagingIdentityRemoteUE_r17__Format.

Record SL_TxResourceReqL2U2N_Relay_r17__Type : Set :=
  make__SL_TxResourceReqL2U2N_Relay_r17__Type {
    SL_TxResourceReqL2U2N_Relay_r17__sl_DestinationIdentityL2U2N_r17 : option SL_DestinationIdentity_r16__Type ;
    SL_TxResourceReqL2U2N_Relay_r17__sl_TxInterestedFreqListL2U2N_r17 : SL_TxInterestedFreqList_r16__Type ;
    SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17 : SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Type ;
    SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17 : option SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type ;
    SL_TxResourceReqL2U2N_Relay_r17__sl_PagingIdentityRemoteUE_r17 : option SL_PagingIdentityRemoteUE_r17__Type ;
    SL_TxResourceReqL2U2N_Relay_r17__sl_CapabilityInformationSidelink_r17 : option octet_string ;
}.
Definition SL_TxResourceReqL2U2N_Relay_r17__root_list : list seq_elem := (
 Opt SL_DestinationIdentity_r16__Type SL_DestinationIdentity_r16__cond ::
 Nor SL_TxInterestedFreqList_r16__Type SL_TxInterestedFreqList_r16__cond ::
 Nor SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Type SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__cond ::
 Opt SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__cond ::
 Opt SL_PagingIdentityRemoteUE_r17__Type SL_PagingIdentityRemoteUE_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition SL_TxResourceReqL2U2N_Relay_r17__ext_list : list typ := (
  nil).
Definition SL_TxResourceReqL2U2N_Relay_r17__cond (z : SL_TxResourceReqL2U2N_Relay_r17__Type) := 
(  opt_cond SL_DestinationIdentity_r16__cond (SL_TxResourceReqL2U2N_Relay_r17__sl_DestinationIdentityL2U2N_r17 z) /\
  SL_TxInterestedFreqList_r16__cond (SL_TxResourceReqL2U2N_Relay_r17__sl_TxInterestedFreqListL2U2N_r17 z) /\
  SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__cond (SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17 z) /\
  opt_cond SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__cond (SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17 z) /\
  opt_cond SL_PagingIdentityRemoteUE_r17__cond (SL_TxResourceReqL2U2N_Relay_r17__sl_PagingIdentityRemoteUE_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SL_TxResourceReqL2U2N_Relay_r17__sl_CapabilityInformationSidelink_r17 z) /\
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
Definition SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Format : T_Format SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Type SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__cond := seq_of_format SL_TypeTxSync_r16__Format 1 maxNrofFreqSL_r16 SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__helper1 SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__helper2.

Opaque SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__cond SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Format.

Definition SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Format : T_Format SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__nat__Format SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F1 SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F2 SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F1F2 SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__F2F1.

Opaque SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__cond SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Format.


Definition SL_TxResourceReqL2U2N_Relay_r17__root_Format_Type := Eval cbn in seq_format_prod SL_TxResourceReqL2U2N_Relay_r17__root_list.
Definition SL_TxResourceReqL2U2N_Relay_r17__root_Format_list : SL_TxResourceReqL2U2N_Relay_r17__root_Format_Type :=
  (SL_DestinationIdentity_r16__Format, (SL_TxInterestedFreqList_r16__Format, (SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17__Format, (SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17__Format, (SL_PagingIdentityRemoteUE_r17__Format, (octet_string_nc__Format, unit_format)))))).

Definition SL_TxResourceReqL2U2N_Relay_r17__ext_Format_Type := Eval cbn in get_formats SL_TxResourceReqL2U2N_Relay_r17__ext_list.
Definition SL_TxResourceReqL2U2N_Relay_r17__ext_Format_list : SL_TxResourceReqL2U2N_Relay_r17__ext_Format_Type :=
  unit__Format.

Definition SL_TxResourceReqL2U2N_Relay_r17__list_type : Set := (seq_type SL_TxResourceReqL2U2N_Relay_r17__root_list) * (seq_ext_type SL_TxResourceReqL2U2N_Relay_r17__ext_list).
Definition SL_TxResourceReqL2U2N_Relay_r17__list_cond (z : SL_TxResourceReqL2U2N_Relay_r17__list_type) : Prop :=
        (seq_cond SL_TxResourceReqL2U2N_Relay_r17__root_list (fst z)) /\ (seq_ext_cond SL_TxResourceReqL2U2N_Relay_r17__ext_list (snd z)).
Definition SL_TxResourceReqL2U2N_Relay_r17__list_format : T_Format SL_TxResourceReqL2U2N_Relay_r17__list_type SL_TxResourceReqL2U2N_Relay_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SL_TxResourceReqL2U2N_Relay_r17__root_list SL_TxResourceReqL2U2N_Relay_r17__root_Format_list SL_TxResourceReqL2U2N_Relay_r17__ext_list SL_TxResourceReqL2U2N_Relay_r17__ext_Format_list.

Opaque SL_TxResourceReqL2U2N_Relay_r17__list_format.
Definition SL_TxResourceReqL2U2N_Relay_r17__F1 (z : SL_TxResourceReqL2U2N_Relay_r17__Type) : SL_TxResourceReqL2U2N_Relay_r17__list_type :=
  (((SL_TxResourceReqL2U2N_Relay_r17__sl_DestinationIdentityL2U2N_r17 z, (SL_TxResourceReqL2U2N_Relay_r17__sl_TxInterestedFreqListL2U2N_r17 z, (SL_TxResourceReqL2U2N_Relay_r17__sl_TypeTxSyncListL2U2N_r17 z, (SL_TxResourceReqL2U2N_Relay_r17__sl_LocalID_Request_r17 z, (SL_TxResourceReqL2U2N_Relay_r17__sl_PagingIdentityRemoteUE_r17 z, (SL_TxResourceReqL2U2N_Relay_r17__sl_CapabilityInformationSidelink_r17 z, tt))))))), (
tt)).
Definition SL_TxResourceReqL2U2N_Relay_r17__F2 (y : SL_TxResourceReqL2U2N_Relay_r17__list_type) : SL_TxResourceReqL2U2N_Relay_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__SL_TxResourceReqL2U2N_Relay_r17__Type j0 j1 j2 j3 j4 j5
  end.
Definition SL_TxResourceReqL2U2N_Relay_r17__helper1 : (forall a : SL_TxResourceReqL2U2N_Relay_r17__Type, SL_TxResourceReqL2U2N_Relay_r17__cond a -> SL_TxResourceReqL2U2N_Relay_r17__list_cond (SL_TxResourceReqL2U2N_Relay_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_TxResourceReqL2U2N_Relay_r17__helper2 : (forall a : SL_TxResourceReqL2U2N_Relay_r17__Type, SL_TxResourceReqL2U2N_Relay_r17__F2 (SL_TxResourceReqL2U2N_Relay_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_TxResourceReqL2U2N_Relay_r17__helper3 : (forall b : SL_TxResourceReqL2U2N_Relay_r17__list_type, SL_TxResourceReqL2U2N_Relay_r17__list_cond b -> SL_TxResourceReqL2U2N_Relay_r17__cond (SL_TxResourceReqL2U2N_Relay_r17__F2 b) /\ SL_TxResourceReqL2U2N_Relay_r17__F1 (SL_TxResourceReqL2U2N_Relay_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_TxResourceReqL2U2N_Relay_r17__cond, SL_TxResourceReqL2U2N_Relay_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_TxResourceReqL2U2N_Relay_r17__Format : T_Format SL_TxResourceReqL2U2N_Relay_r17__Type SL_TxResourceReqL2U2N_Relay_r17__cond :=
 proj2_format SL_TxResourceReqL2U2N_Relay_r17__cond SL_TxResourceReqL2U2N_Relay_r17__list_format  SL_TxResourceReqL2U2N_Relay_r17__F1 SL_TxResourceReqL2U2N_Relay_r17__F2 SL_TxResourceReqL2U2N_Relay_r17__helper1 SL_TxResourceReqL2U2N_Relay_r17__helper2 SL_TxResourceReqL2U2N_Relay_r17__helper3.

Opaque SL_TxResourceReqL2U2N_Relay_r17__cond SL_TxResourceReqL2U2N_Relay_r17__Format.

