Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Lemma DCP_Config_r16__ps_Offset_r16__helper1 : (1 <= 120)%Z.  lia. Qed.
Lemma DCP_Config_r16__ps_Offset_r16__helper2 : to_bit_sz (Z.to_nat (120 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (120 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DCP_Config_r16__ps_Offset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DCP_Config_r16__ps_Offset_r16__Type := Z.
Definition DCP_Config_r16__ps_Offset_r16__cond := (fun z => (1 <= z <= 120)%Z).
Lemma DCP_Config_r16__sizeDCI_2_6_r16__helper1 : (1 <= maxDCI_2_6_Size_r16)%Z. unfold maxDCI_2_6_Size_r16.
 lia. Qed.
Lemma DCP_Config_r16__sizeDCI_2_6_r16__helper2 : to_bit_sz (Z.to_nat (maxDCI_2_6_Size_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDCI_2_6_Size_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DCP_Config_r16__sizeDCI_2_6_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DCP_Config_r16__sizeDCI_2_6_r16__Type := Z.
Definition DCP_Config_r16__sizeDCI_2_6_r16__cond := (fun z => (1 <= z <= maxDCI_2_6_Size_r16)%Z).
Lemma DCP_Config_r16__ps_PositionDCI_2_6_r16__helper1 : (0 <= maxDCI_2_6_Size_1_r16)%Z. unfold maxDCI_2_6_Size_1_r16.
 lia. Qed.
Lemma DCP_Config_r16__ps_PositionDCI_2_6_r16__helper2 : to_bit_sz (Z.to_nat (maxDCI_2_6_Size_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDCI_2_6_Size_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply DCP_Config_r16__ps_PositionDCI_2_6_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DCP_Config_r16__ps_PositionDCI_2_6_r16__Type := Z.
Definition DCP_Config_r16__ps_PositionDCI_2_6_r16__cond := (fun z => (0 <= z <= maxDCI_2_6_Size_1_r16)%Z).
Inductive DCP_Config_r16__ps_WakeUp_r16__Type : Set :=
 | DCP_Config_r16__ps_WakeUp_r16__true
.
Definition DCP_Config_r16__ps_WakeUp_r16__cond := (fun (_ : DCP_Config_r16__ps_WakeUp_r16__Type) => True).
Lemma DCP_Config_r16__ps_WakeUp_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DCP_Config_r16__ps_WakeUp_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DCP_Config_r16__ps_WakeUp_r16__nat__helper.

Definition DCP_Config_r16__ps_WakeUp_r16__F1 t :=
  match t with
  | DCP_Config_r16__ps_WakeUp_r16__true => 0
  end.
Definition DCP_Config_r16__ps_WakeUp_r16__F2 n :=
  match n with
  | 0 => DCP_Config_r16__ps_WakeUp_r16__true
  | _ => DCP_Config_r16__ps_WakeUp_r16__true
  end.
Lemma DCP_Config_r16__ps_WakeUp_r16__F1F2 : forall x : DCP_Config_r16__ps_WakeUp_r16__Type, (DCP_Config_r16__ps_WakeUp_r16__F1 x <= 0) /\ DCP_Config_r16__ps_WakeUp_r16__F2 (DCP_Config_r16__ps_WakeUp_r16__F1 x) = x. imp_solve. Qed.
Lemma DCP_Config_r16__ps_WakeUp_r16__F2F1 : forall (y : nat) (H : y <= 0), DCP_Config_r16__ps_WakeUp_r16__F1 (DCP_Config_r16__ps_WakeUp_r16__F2 y) = y. enum_solve H y. Qed.

Inductive DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Type : Set :=
 | DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__true
.
Definition DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__cond := (fun (_ : DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Type) => True).
Lemma DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__nat__helper.

Definition DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F1 t :=
  match t with
  | DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__true => 0
  end.
Definition DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F2 n :=
  match n with
  | 0 => DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__true
  | _ => DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__true
  end.
Lemma DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F1F2 : forall x : DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Type, (DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F1 x <= 0) /\ DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F2 (DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F1 x) = x. imp_solve. Qed.
Lemma DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F2F1 : forall (y : nat) (H : y <= 0), DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F1 (DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Type : Set :=
 | DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__true
.
Definition DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__cond := (fun (_ : DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Type) => True).
Lemma DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__nat__helper.

Definition DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F1 t :=
  match t with
  | DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__true => 0
  end.
Definition DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F2 n :=
  match n with
  | 0 => DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__true
  | _ => DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__true
  end.
Lemma DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F1F2 : forall x : DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Type, (DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F1 x <= 0) /\ DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F2 (DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F1 x) = x. imp_solve. Qed.
Lemma DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F2F1 : forall (y : nat) (H : y <= 0), DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F1 (DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F2 y) = y. enum_solve H y. Qed.

Record DCP_Config_r16__Type : Set :=
  make__DCP_Config_r16__Type {
    DCP_Config_r16__ps_RNTI_r16 : RNTI_Value__Type ;
    DCP_Config_r16__ps_Offset_r16 : Z ;
    DCP_Config_r16__sizeDCI_2_6_r16 : Z ;
    DCP_Config_r16__ps_PositionDCI_2_6_r16 : Z ;
    DCP_Config_r16__ps_WakeUp_r16 : option DCP_Config_r16__ps_WakeUp_r16__Type ;
    DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16 : option DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Type ;
    DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16 : option DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Type ;
}.
Definition DCP_Config_r16__list := (
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Nor Z DCP_Config_r16__ps_Offset_r16__cond ::
 Nor Z DCP_Config_r16__sizeDCI_2_6_r16__cond ::
 Nor Z DCP_Config_r16__ps_PositionDCI_2_6_r16__cond ::
 Opt DCP_Config_r16__ps_WakeUp_r16__Type DCP_Config_r16__ps_WakeUp_r16__cond ::
 Opt DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Type DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__cond ::
 Opt DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Type DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__cond ::
 nil).
Definition DCP_Config_r16__cond z := 
  RNTI_Value__cond (DCP_Config_r16__ps_RNTI_r16 z) /\
  DCP_Config_r16__ps_Offset_r16__cond (DCP_Config_r16__ps_Offset_r16 z) /\
  DCP_Config_r16__sizeDCI_2_6_r16__cond (DCP_Config_r16__sizeDCI_2_6_r16 z) /\
  DCP_Config_r16__ps_PositionDCI_2_6_r16__cond (DCP_Config_r16__ps_PositionDCI_2_6_r16 z) /\
  opt_cond DCP_Config_r16__ps_WakeUp_r16__cond (DCP_Config_r16__ps_WakeUp_r16 z) /\
  opt_cond DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__cond (DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16 z) /\
  opt_cond DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__cond (DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16 z) /\
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
Definition DCP_Config_r16__ps_Offset_r16__Format : T_Format Z DCP_Config_r16__ps_Offset_r16__cond :=
 ranged_int_format (1) (120) DCP_Config_r16__ps_Offset_r16__helper1 DCP_Config_r16__ps_Offset_r16__helper2.

Opaque DCP_Config_r16__ps_Offset_r16__cond DCP_Config_r16__ps_Offset_r16__Format.

Definition DCP_Config_r16__sizeDCI_2_6_r16__Format : T_Format Z DCP_Config_r16__sizeDCI_2_6_r16__cond :=
 ranged_int_format (1) (maxDCI_2_6_Size_r16) DCP_Config_r16__sizeDCI_2_6_r16__helper1 DCP_Config_r16__sizeDCI_2_6_r16__helper2.

Opaque DCP_Config_r16__sizeDCI_2_6_r16__cond DCP_Config_r16__sizeDCI_2_6_r16__Format.

Definition DCP_Config_r16__ps_PositionDCI_2_6_r16__Format : T_Format Z DCP_Config_r16__ps_PositionDCI_2_6_r16__cond :=
 ranged_int_format (0) (maxDCI_2_6_Size_1_r16) DCP_Config_r16__ps_PositionDCI_2_6_r16__helper1 DCP_Config_r16__ps_PositionDCI_2_6_r16__helper2.

Opaque DCP_Config_r16__ps_PositionDCI_2_6_r16__cond DCP_Config_r16__ps_PositionDCI_2_6_r16__Format.

Definition DCP_Config_r16__ps_WakeUp_r16__Format : T_Format DCP_Config_r16__ps_WakeUp_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DCP_Config_r16__ps_WakeUp_r16__nat__Format DCP_Config_r16__ps_WakeUp_r16__F1 DCP_Config_r16__ps_WakeUp_r16__F2 DCP_Config_r16__ps_WakeUp_r16__F1F2 DCP_Config_r16__ps_WakeUp_r16__F2F1.

Opaque DCP_Config_r16__ps_WakeUp_r16__cond DCP_Config_r16__ps_WakeUp_r16__Format.

Definition DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Format : T_Format DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__nat__Format DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F1 DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F2 DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F1F2 DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__F2F1.

Opaque DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__cond DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Format.

Definition DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Format : T_Format DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__nat__Format DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F1 DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F2 DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F1F2 DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__F2F1.

Opaque DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__cond DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Format.


Definition DCP_Config_r16__Format_Type := Eval cbn in seq_format_prod DCP_Config_r16__list.
Definition DCP_Config_r16__Format_list : DCP_Config_r16__Format_Type :=
  (RNTI_Value__Format, (DCP_Config_r16__ps_Offset_r16__Format, (DCP_Config_r16__sizeDCI_2_6_r16__Format, (DCP_Config_r16__ps_PositionDCI_2_6_r16__Format, (DCP_Config_r16__ps_WakeUp_r16__Format, (DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16__Format, (DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16__Format, unit_format))))))).
Definition DCP_Config_r16__list__Format := (*Eval compute in *) seq_format DCP_Config_r16__list DCP_Config_r16__Format_list.
Definition DCP_Config_r16__F1 z :=
  (DCP_Config_r16__ps_RNTI_r16 z, (DCP_Config_r16__ps_Offset_r16 z, (DCP_Config_r16__sizeDCI_2_6_r16 z, (DCP_Config_r16__ps_PositionDCI_2_6_r16 z, (DCP_Config_r16__ps_WakeUp_r16 z, (DCP_Config_r16__ps_TransmitPeriodicL1_RSRP_r16 z, (DCP_Config_r16__ps_TransmitOtherPeriodicCSI_r16 z, tt))))))).
Definition DCP_Config_r16__F2 (y : seq_type DCP_Config_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__DCP_Config_r16__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma DCP_Config_r16__F1F2_cond (z : DCP_Config_r16__Type)
  : DCP_Config_r16__cond z ->
  (seq_cond DCP_Config_r16__list (DCP_Config_r16__F1 z)).
intro H. unfold DCP_Config_r16__cond in H. simpl. auto. Qed.
Lemma DCP_Config_r16__F1F2_cond2 (z : DCP_Config_r16__Type)
 : DCP_Config_r16__F2 (DCP_Config_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DCP_Config_r16__F2F1_cond (y : seq_type DCP_Config_r16__list)
  : seq_cond DCP_Config_r16__list y ->
 (DCP_Config_r16__cond (DCP_Config_r16__F2 y)) /\  DCP_Config_r16__F1 (DCP_Config_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DCP_Config_r16__cond. simpl in *. auto.
 - simpl. unfold DCP_Config_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DCP_Config_r16__Format : T_Format DCP_Config_r16__Type DCP_Config_r16__cond :=
        proj2_format  DCP_Config_r16__cond DCP_Config_r16__list__Format
    DCP_Config_r16__F1 DCP_Config_r16__F2 DCP_Config_r16__F1F2_cond  DCP_Config_r16__F1F2_cond2 DCP_Config_r16__F2F1_cond.
Opaque DCP_Config_r16__cond DCP_Config_r16__Format.

