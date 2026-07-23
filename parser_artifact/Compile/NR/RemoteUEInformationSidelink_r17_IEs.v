Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SL_RequestedSIB_List_r17.
Definition RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__Type := SetupRelease__Type SL_RequestedSIB_List_r17__Type.
Definition RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__cond := SetupRelease__cond _ SL_RequestedSIB_List_r17__cond.
Definition RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__Format : T_Format RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__Type RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__cond := SetupRelease__Format _ _ SL_RequestedSIB_List_r17__Format.
Opaque RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__cond RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_PagingInfo_RemoteUE_r17.
Definition RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__Type := SetupRelease__Type SL_PagingInfo_RemoteUE_r17__Type.
Definition RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__cond := SetupRelease__cond _ SL_PagingInfo_RemoteUE_r17__cond.
Definition RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__Format : T_Format RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__Type RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__cond := SetupRelease__Format _ _ SL_PagingInfo_RemoteUE_r17__Format.
Opaque RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__cond RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__Format.

Record RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type : Set := make__RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type {}.
Definition RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__cond (z : RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type) := True.
Record RemoteUEInformationSidelink_r17_IEs__Type : Set :=
  make__RemoteUEInformationSidelink_r17_IEs__Type {
    RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17 : option RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__Type ;
    RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17 : option RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__Type ;
    RemoteUEInformationSidelink_r17_IEs__lateNonCriticalExtension : option octet_string ;
    RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension : option RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type ;
}.
Definition RemoteUEInformationSidelink_r17_IEs__list := (
 Opt RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__Type RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__cond ::
 Opt RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__Type RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__cond ::
 nil).
Definition RemoteUEInformationSidelink_r17_IEs__cond z := 
  opt_cond RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__cond (RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17 z) /\
  opt_cond RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__cond (RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RemoteUEInformationSidelink_r17_IEs__lateNonCriticalExtension z) /\
  opt_cond RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__cond (RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension z) /\
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
Opaque RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__cond RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__Format.

Opaque RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__cond RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__Format.

Definition RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__helper : forall a : RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type, True -> True /\ make__RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Format : T_Format RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Type)
    RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__cond RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Format.


Definition RemoteUEInformationSidelink_r17_IEs__Format_Type := Eval cbn in seq_format_prod RemoteUEInformationSidelink_r17_IEs__list.
Definition RemoteUEInformationSidelink_r17_IEs__Format_list : RemoteUEInformationSidelink_r17_IEs__Format_Type :=
  (RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17__Format, (RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17__Format, (octet_string_nc__Format, (RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension__Format, unit_format)))).
Definition RemoteUEInformationSidelink_r17_IEs__list__Format := (*Eval compute in *) seq_format RemoteUEInformationSidelink_r17_IEs__list RemoteUEInformationSidelink_r17_IEs__Format_list.
Definition RemoteUEInformationSidelink_r17_IEs__F1 z :=
  (RemoteUEInformationSidelink_r17_IEs__sl_RequestedSIB_List_r17 z, (RemoteUEInformationSidelink_r17_IEs__sl_PagingInfo_RemoteUE_r17 z, (RemoteUEInformationSidelink_r17_IEs__lateNonCriticalExtension z, (RemoteUEInformationSidelink_r17_IEs__nonCriticalExtension z, tt)))).
Definition RemoteUEInformationSidelink_r17_IEs__F2 (y : seq_type RemoteUEInformationSidelink_r17_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__RemoteUEInformationSidelink_r17_IEs__Type i0 i1 i2 i3
  end.
Lemma RemoteUEInformationSidelink_r17_IEs__F1F2_cond (z : RemoteUEInformationSidelink_r17_IEs__Type)
  : RemoteUEInformationSidelink_r17_IEs__cond z ->
  (seq_cond RemoteUEInformationSidelink_r17_IEs__list (RemoteUEInformationSidelink_r17_IEs__F1 z)).
intro H. unfold RemoteUEInformationSidelink_r17_IEs__cond in H. simpl. auto. Qed.
Lemma RemoteUEInformationSidelink_r17_IEs__F1F2_cond2 (z : RemoteUEInformationSidelink_r17_IEs__Type)
 : RemoteUEInformationSidelink_r17_IEs__F2 (RemoteUEInformationSidelink_r17_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RemoteUEInformationSidelink_r17_IEs__F2F1_cond (y : seq_type RemoteUEInformationSidelink_r17_IEs__list)
  : seq_cond RemoteUEInformationSidelink_r17_IEs__list y ->
 (RemoteUEInformationSidelink_r17_IEs__cond (RemoteUEInformationSidelink_r17_IEs__F2 y)) /\  RemoteUEInformationSidelink_r17_IEs__F1 (RemoteUEInformationSidelink_r17_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RemoteUEInformationSidelink_r17_IEs__cond. simpl in *. auto.
 - simpl. unfold RemoteUEInformationSidelink_r17_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RemoteUEInformationSidelink_r17_IEs__Format : T_Format RemoteUEInformationSidelink_r17_IEs__Type RemoteUEInformationSidelink_r17_IEs__cond :=
        proj2_format  RemoteUEInformationSidelink_r17_IEs__cond RemoteUEInformationSidelink_r17_IEs__list__Format
    RemoteUEInformationSidelink_r17_IEs__F1 RemoteUEInformationSidelink_r17_IEs__F2 RemoteUEInformationSidelink_r17_IEs__F1F2_cond  RemoteUEInformationSidelink_r17_IEs__F1F2_cond2 RemoteUEInformationSidelink_r17_IEs__F2F1_cond.
Opaque RemoteUEInformationSidelink_r17_IEs__cond RemoteUEInformationSidelink_r17_IEs__Format.

