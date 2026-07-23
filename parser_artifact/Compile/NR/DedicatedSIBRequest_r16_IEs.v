Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SIB_ReqInfo_r16.

Opaque SIB_ReqInfo_r16__cond SIB_ReqInfo_r16__Format.

Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type := list SIB_ReqInfo_r16__Type.

Lemma DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__helper1 : (0 <= 1 <= maxOnDemandSIB_r16)%Z. unfold maxOnDemandSIB_r16.
 lia. Qed.
Lemma DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__helper2 : to_bit_sz (Z.to_nat (maxOnDemandSIB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxOnDemandSIB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__cond (z : DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxOnDemandSIB_r16)%Z /\ (list_and SIB_ReqInfo_r16__cond z) .

Require Import NR.PosSIB_ReqInfo_r16.

Opaque PosSIB_ReqInfo_r16__cond PosSIB_ReqInfo_r16__Format.

Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type := list PosSIB_ReqInfo_r16__Type.

Lemma DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__helper1 : (0 <= 1 <= maxOnDemandPosSIB_r16)%Z. unfold maxOnDemandPosSIB_r16.
 lia. Qed.
Lemma DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__helper2 : to_bit_sz (Z.to_nat (maxOnDemandPosSIB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxOnDemandPosSIB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__cond (z : DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxOnDemandPosSIB_r16)%Z /\ (list_and PosSIB_ReqInfo_r16__cond z) .

Record DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type : Set :=
  make__DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type {
    DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16 : option DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type ;
    DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16 : option DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type ;
}.
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list := (
 Opt DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__cond ::
 Opt DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__cond ::
 nil).
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond z := 
  opt_cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__cond (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16 z) /\
  opt_cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__cond (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16 z) /\
  True.

Record DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type : Set := make__DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type {}.
Definition DedicatedSIBRequest_r16_IEs__nonCriticalExtension__cond (z : DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type) := True.
Record DedicatedSIBRequest_r16_IEs__Type : Set :=
  make__DedicatedSIBRequest_r16_IEs__Type {
    DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16 : option DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type ;
    DedicatedSIBRequest_r16_IEs__lateNonCriticalExtension : option octet_string ;
    DedicatedSIBRequest_r16_IEs__nonCriticalExtension : option DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type ;
}.
Definition DedicatedSIBRequest_r16_IEs__list := (
 Opt DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type DedicatedSIBRequest_r16_IEs__nonCriticalExtension__cond ::
 nil).
Definition DedicatedSIBRequest_r16_IEs__cond z := 
  opt_cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (DedicatedSIBRequest_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond DedicatedSIBRequest_r16_IEs__nonCriticalExtension__cond (DedicatedSIBRequest_r16_IEs__nonCriticalExtension z) /\
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
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Format : T_Format DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Type DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__cond := seq_of_format SIB_ReqInfo_r16__Format 1 maxOnDemandSIB_r16 DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__helper1 DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__helper2.

Opaque DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Format.

Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Format : T_Format DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Type DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__cond := seq_of_format PosSIB_ReqInfo_r16__Format 1 maxOnDemandPosSIB_r16 DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__helper1 DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__helper2.

Opaque DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Format.


Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format_Type := Eval cbn in seq_format_prod DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list.
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format_list : DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format_Type :=
  (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16__Format, (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16__Format, unit_format)).
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list__Format := (*Eval compute in *) seq_format DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format_list.
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1 z :=
  (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedSIB_List_r16 z, (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__requestedPosSIB_List_r16 z, tt)).
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F2 (y : seq_type DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type i0 i1
  end.
Lemma DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1F2_cond (z : DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type)
  : DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond z ->
  (seq_cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1 z)).
intro H. unfold DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond in H. simpl. auto. Qed.
Lemma DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1F2_cond2 (z : DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type)
 : DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F2 (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F2F1_cond (y : seq_type DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list)
  : seq_cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list y ->
 (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F2 y)) /\  DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1 (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond. simpl in *. auto.
 - simpl. unfold DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format : T_Format DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Type DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond :=
        proj2_format  DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__list__Format
    DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1 DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F2 DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1F2_cond  DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F1F2_cond2 DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__F2F1_cond.
Opaque DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__cond DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format.

Definition DedicatedSIBRequest_r16_IEs__nonCriticalExtension__helper : forall a : DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type, True -> True /\ make__DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Format : T_Format DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type DedicatedSIBRequest_r16_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Type)
    DedicatedSIBRequest_r16_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque DedicatedSIBRequest_r16_IEs__nonCriticalExtension__cond DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Format.


Definition DedicatedSIBRequest_r16_IEs__Format_Type := Eval cbn in seq_format_prod DedicatedSIBRequest_r16_IEs__list.
Definition DedicatedSIBRequest_r16_IEs__Format_list : DedicatedSIBRequest_r16_IEs__Format_Type :=
  (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16__Format, (octet_string_nc__Format, (DedicatedSIBRequest_r16_IEs__nonCriticalExtension__Format, unit_format))).
Definition DedicatedSIBRequest_r16_IEs__list__Format := (*Eval compute in *) seq_format DedicatedSIBRequest_r16_IEs__list DedicatedSIBRequest_r16_IEs__Format_list.
Definition DedicatedSIBRequest_r16_IEs__F1 z :=
  (DedicatedSIBRequest_r16_IEs__onDemandSIB_RequestList_r16 z, (DedicatedSIBRequest_r16_IEs__lateNonCriticalExtension z, (DedicatedSIBRequest_r16_IEs__nonCriticalExtension z, tt))).
Definition DedicatedSIBRequest_r16_IEs__F2 (y : seq_type DedicatedSIBRequest_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__DedicatedSIBRequest_r16_IEs__Type i0 i1 i2
  end.
Lemma DedicatedSIBRequest_r16_IEs__F1F2_cond (z : DedicatedSIBRequest_r16_IEs__Type)
  : DedicatedSIBRequest_r16_IEs__cond z ->
  (seq_cond DedicatedSIBRequest_r16_IEs__list (DedicatedSIBRequest_r16_IEs__F1 z)).
intro H. unfold DedicatedSIBRequest_r16_IEs__cond in H. simpl. auto. Qed.
Lemma DedicatedSIBRequest_r16_IEs__F1F2_cond2 (z : DedicatedSIBRequest_r16_IEs__Type)
 : DedicatedSIBRequest_r16_IEs__F2 (DedicatedSIBRequest_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DedicatedSIBRequest_r16_IEs__F2F1_cond (y : seq_type DedicatedSIBRequest_r16_IEs__list)
  : seq_cond DedicatedSIBRequest_r16_IEs__list y ->
 (DedicatedSIBRequest_r16_IEs__cond (DedicatedSIBRequest_r16_IEs__F2 y)) /\  DedicatedSIBRequest_r16_IEs__F1 (DedicatedSIBRequest_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DedicatedSIBRequest_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold DedicatedSIBRequest_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DedicatedSIBRequest_r16_IEs__Format : T_Format DedicatedSIBRequest_r16_IEs__Type DedicatedSIBRequest_r16_IEs__cond :=
        proj2_format  DedicatedSIBRequest_r16_IEs__cond DedicatedSIBRequest_r16_IEs__list__Format
    DedicatedSIBRequest_r16_IEs__F1 DedicatedSIBRequest_r16_IEs__F2 DedicatedSIBRequest_r16_IEs__F1F2_cond  DedicatedSIBRequest_r16_IEs__F1F2_cond2 DedicatedSIBRequest_r16_IEs__F2F1_cond.
Opaque DedicatedSIBRequest_r16_IEs__cond DedicatedSIBRequest_r16_IEs__Format.

