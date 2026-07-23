Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Type : Set :=
 | FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__yes
 | FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__no
.
Definition FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__cond := (fun (_ : FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Type) => True).
Lemma FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__nat__helper.

Definition FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F1 t :=
  match t with
  | FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__yes => 0
  | FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__no => 1
  end.
Definition FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__yes
  | 1 => FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__no
  | _ => FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__yes
  end.
Lemma FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F1F2 : forall x : FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Type, (FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F1 x <= 1) /\ FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F2 (FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F2F1 : forall (y : nat) (H : y <= 1), FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F1 (FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Type : Set :=
 | FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__supported
.
Definition FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__cond := (fun (_ : FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Type) => True).
Lemma FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__nat__helper.

Definition FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F1 t :=
  match t with
  | FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__supported => 0
  end.
Definition FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__supported
  | _ => FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__supported
  end.
Lemma FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F1F2 : forall x : FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Type, (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F1 x <= 0) /\ FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F2 (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F1 (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F2 y) = y. enum_solve H y. Qed.

Lemma FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__Type := Z.
Definition FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__cond := (fun z => (1 <= z <= 8)%Z).
Inductive FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Type : Set :=
 | FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__supported
.
Definition FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__cond := (fun (_ : FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Type) => True).
Lemma FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__nat__helper.

Definition FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F1 t :=
  match t with
  | FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__supported => 0
  end.
Definition FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__supported
  | _ => FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__supported
  end.
Lemma FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F1F2 : forall x : FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Type, (FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F1 x <= 0) /\ FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F2 (FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F1 (FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetDownlinkPerCC_v1730__Type : Set :=
  make__FeatureSetDownlinkPerCC_v1730__Type {
    FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17 : option FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Type ;
    FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17 : option FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Type ;
    FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17 : option Z ;
    FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17 : option FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Type ;
}.
Definition FeatureSetDownlinkPerCC_v1730__list := (
 Opt FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Type FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__cond ::
 Opt FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Type FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__cond ::
 Opt Z FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__cond ::
 Opt FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Type FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__cond ::
 nil).
Definition FeatureSetDownlinkPerCC_v1730__cond z := 
  opt_cond FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__cond (FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17 z) /\
  opt_cond FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__cond (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17 z) /\
  opt_cond FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__cond (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17 z) /\
  opt_cond FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__cond (FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17 z) /\
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
Definition FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Format : T_Format FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__nat__Format FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F1 FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F2 FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F1F2 FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__F2F1.

Opaque FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__cond FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Format.

Definition FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Format : T_Format FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__nat__Format FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F1 FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F2 FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F1F2 FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__F2F1.

Opaque FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__cond FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Format.

Definition FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__Format : T_Format Z FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__cond :=
 ranged_int_format (1) (8) FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__helper1 FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__helper2.

Opaque FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__cond FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__Format.

Definition FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Format : T_Format FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__nat__Format FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F1 FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F2 FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F1F2 FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__F2F1.

Opaque FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__cond FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Format.


Definition FeatureSetDownlinkPerCC_v1730__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlinkPerCC_v1730__list.
Definition FeatureSetDownlinkPerCC_v1730__Format_list : FeatureSetDownlinkPerCC_v1730__Format_Type :=
  (FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17__Format, (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17__Format, (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17__Format, (FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17__Format, unit_format)))).
Definition FeatureSetDownlinkPerCC_v1730__list__Format := (*Eval compute in *) seq_format FeatureSetDownlinkPerCC_v1730__list FeatureSetDownlinkPerCC_v1730__Format_list.
Definition FeatureSetDownlinkPerCC_v1730__F1 z :=
  (FeatureSetDownlinkPerCC_v1730__intraSlotTDM_UnicastGroupCommonPDSCH_r17 z, (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCell_r17 z, (FeatureSetDownlinkPerCC_v1730__sps_MulticastSCellMultiConfig_r17 z, (FeatureSetDownlinkPerCC_v1730__dci_BroadcastWith16Repetitions_r17 z, tt)))).
Definition FeatureSetDownlinkPerCC_v1730__F2 (y : seq_type FeatureSetDownlinkPerCC_v1730__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__FeatureSetDownlinkPerCC_v1730__Type i0 i1 i2 i3
  end.
Lemma FeatureSetDownlinkPerCC_v1730__F1F2_cond (z : FeatureSetDownlinkPerCC_v1730__Type)
  : FeatureSetDownlinkPerCC_v1730__cond z ->
  (seq_cond FeatureSetDownlinkPerCC_v1730__list (FeatureSetDownlinkPerCC_v1730__F1 z)).
intro H. unfold FeatureSetDownlinkPerCC_v1730__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlinkPerCC_v1730__F1F2_cond2 (z : FeatureSetDownlinkPerCC_v1730__Type)
 : FeatureSetDownlinkPerCC_v1730__F2 (FeatureSetDownlinkPerCC_v1730__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlinkPerCC_v1730__F2F1_cond (y : seq_type FeatureSetDownlinkPerCC_v1730__list)
  : seq_cond FeatureSetDownlinkPerCC_v1730__list y ->
 (FeatureSetDownlinkPerCC_v1730__cond (FeatureSetDownlinkPerCC_v1730__F2 y)) /\  FeatureSetDownlinkPerCC_v1730__F1 (FeatureSetDownlinkPerCC_v1730__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlinkPerCC_v1730__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlinkPerCC_v1730__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlinkPerCC_v1730__Format : T_Format FeatureSetDownlinkPerCC_v1730__Type FeatureSetDownlinkPerCC_v1730__cond :=
        proj2_format  FeatureSetDownlinkPerCC_v1730__cond FeatureSetDownlinkPerCC_v1730__list__Format
    FeatureSetDownlinkPerCC_v1730__F1 FeatureSetDownlinkPerCC_v1730__F2 FeatureSetDownlinkPerCC_v1730__F1F2_cond  FeatureSetDownlinkPerCC_v1730__F1F2_cond2 FeatureSetDownlinkPerCC_v1730__F2F1_cond.
Opaque FeatureSetDownlinkPerCC_v1730__cond FeatureSetDownlinkPerCC_v1730__Format.

