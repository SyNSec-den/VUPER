Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_MTC_AdditionalPCI_r17.

Opaque SSB_MTC_AdditionalPCI_r17__cond SSB_MTC_AdditionalPCI_r17__Format.

Definition MIMOParam_r17__additionalPCI_ToAddModList_r17__Type := list SSB_MTC_AdditionalPCI_r17__Type.

Lemma MIMOParam_r17__additionalPCI_ToAddModList_r17__helper1 : (0 <= 1 <= maxNrofAdditionalPCI_r17)%Z. unfold maxNrofAdditionalPCI_r17.
 lia. Qed.
Lemma MIMOParam_r17__additionalPCI_ToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofAdditionalPCI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAdditionalPCI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMOParam_r17__additionalPCI_ToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMOParam_r17__additionalPCI_ToAddModList_r17__cond (z : MIMOParam_r17__additionalPCI_ToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAdditionalPCI_r17)%Z /\ (list_and SSB_MTC_AdditionalPCI_r17__cond z) .

Require Import NR.AdditionalPCIIndex_r17.

Opaque AdditionalPCIIndex_r17__cond AdditionalPCIIndex_r17__Format.

Definition MIMOParam_r17__additionalPCI_ToReleaseList_r17__Type := list AdditionalPCIIndex_r17__Type.

Lemma MIMOParam_r17__additionalPCI_ToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofAdditionalPCI_r17)%Z. unfold maxNrofAdditionalPCI_r17.
 lia. Qed.
Lemma MIMOParam_r17__additionalPCI_ToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofAdditionalPCI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAdditionalPCI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMOParam_r17__additionalPCI_ToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMOParam_r17__additionalPCI_ToReleaseList_r17__cond (z : MIMOParam_r17__additionalPCI_ToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAdditionalPCI_r17)%Z /\ (list_and AdditionalPCIIndex_r17__cond z) .

Inductive MIMOParam_r17__unifiedTCI_StateType_r17__Type : Set :=
 | MIMOParam_r17__unifiedTCI_StateType_r17__separate
 | MIMOParam_r17__unifiedTCI_StateType_r17__joint
.
Definition MIMOParam_r17__unifiedTCI_StateType_r17__cond := (fun (_ : MIMOParam_r17__unifiedTCI_StateType_r17__Type) => True).
Lemma MIMOParam_r17__unifiedTCI_StateType_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMOParam_r17__unifiedTCI_StateType_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMOParam_r17__unifiedTCI_StateType_r17__nat__helper.

Definition MIMOParam_r17__unifiedTCI_StateType_r17__F1 t :=
  match t with
  | MIMOParam_r17__unifiedTCI_StateType_r17__separate => 0
  | MIMOParam_r17__unifiedTCI_StateType_r17__joint => 1
  end.
Definition MIMOParam_r17__unifiedTCI_StateType_r17__F2 n :=
  match n with
  | 0 => MIMOParam_r17__unifiedTCI_StateType_r17__separate
  | 1 => MIMOParam_r17__unifiedTCI_StateType_r17__joint
  | _ => MIMOParam_r17__unifiedTCI_StateType_r17__separate
  end.
Lemma MIMOParam_r17__unifiedTCI_StateType_r17__F1F2 : forall x : MIMOParam_r17__unifiedTCI_StateType_r17__Type, (MIMOParam_r17__unifiedTCI_StateType_r17__F1 x <= 1) /\ MIMOParam_r17__unifiedTCI_StateType_r17__F2 (MIMOParam_r17__unifiedTCI_StateType_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMOParam_r17__unifiedTCI_StateType_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMOParam_r17__unifiedTCI_StateType_r17__F1 (MIMOParam_r17__unifiedTCI_StateType_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.Uplink_powerControl_r17.

Opaque Uplink_powerControl_r17__cond Uplink_powerControl_r17__Format.

Definition MIMOParam_r17__uplink_PowerControlToAddModList_r17__Type := list Uplink_powerControl_r17__Type.

Lemma MIMOParam_r17__uplink_PowerControlToAddModList_r17__helper1 : (0 <= 1 <= maxUL_TCI_r17)%Z. unfold maxUL_TCI_r17.
 lia. Qed.
Lemma MIMOParam_r17__uplink_PowerControlToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxUL_TCI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUL_TCI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMOParam_r17__uplink_PowerControlToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMOParam_r17__uplink_PowerControlToAddModList_r17__cond (z : MIMOParam_r17__uplink_PowerControlToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxUL_TCI_r17)%Z /\ (list_and Uplink_powerControl_r17__cond z) .

Require Import NR.Uplink_powerControlId_r17.

Opaque Uplink_powerControlId_r17__cond Uplink_powerControlId_r17__Format.

Definition MIMOParam_r17__uplink_PowerControlToReleaseList_r17__Type := list Uplink_powerControlId_r17__Type.

Lemma MIMOParam_r17__uplink_PowerControlToReleaseList_r17__helper1 : (0 <= 1 <= maxUL_TCI_r17)%Z. unfold maxUL_TCI_r17.
 lia. Qed.
Lemma MIMOParam_r17__uplink_PowerControlToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxUL_TCI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUL_TCI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMOParam_r17__uplink_PowerControlToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMOParam_r17__uplink_PowerControlToReleaseList_r17__cond (z : MIMOParam_r17__uplink_PowerControlToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxUL_TCI_r17)%Z /\ (list_and Uplink_powerControlId_r17__cond z) .

Inductive MIMOParam_r17__sfnSchemePDCCH_r17__Type : Set :=
 | MIMOParam_r17__sfnSchemePDCCH_r17__sfnSchemeA
 | MIMOParam_r17__sfnSchemePDCCH_r17__sfnSchemeB
.
Definition MIMOParam_r17__sfnSchemePDCCH_r17__cond := (fun (_ : MIMOParam_r17__sfnSchemePDCCH_r17__Type) => True).
Lemma MIMOParam_r17__sfnSchemePDCCH_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMOParam_r17__sfnSchemePDCCH_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMOParam_r17__sfnSchemePDCCH_r17__nat__helper.

Definition MIMOParam_r17__sfnSchemePDCCH_r17__F1 t :=
  match t with
  | MIMOParam_r17__sfnSchemePDCCH_r17__sfnSchemeA => 0
  | MIMOParam_r17__sfnSchemePDCCH_r17__sfnSchemeB => 1
  end.
Definition MIMOParam_r17__sfnSchemePDCCH_r17__F2 n :=
  match n with
  | 0 => MIMOParam_r17__sfnSchemePDCCH_r17__sfnSchemeA
  | 1 => MIMOParam_r17__sfnSchemePDCCH_r17__sfnSchemeB
  | _ => MIMOParam_r17__sfnSchemePDCCH_r17__sfnSchemeA
  end.
Lemma MIMOParam_r17__sfnSchemePDCCH_r17__F1F2 : forall x : MIMOParam_r17__sfnSchemePDCCH_r17__Type, (MIMOParam_r17__sfnSchemePDCCH_r17__F1 x <= 1) /\ MIMOParam_r17__sfnSchemePDCCH_r17__F2 (MIMOParam_r17__sfnSchemePDCCH_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMOParam_r17__sfnSchemePDCCH_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMOParam_r17__sfnSchemePDCCH_r17__F1 (MIMOParam_r17__sfnSchemePDCCH_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMOParam_r17__sfnSchemePDSCH_r17__Type : Set :=
 | MIMOParam_r17__sfnSchemePDSCH_r17__sfnSchemeA
 | MIMOParam_r17__sfnSchemePDSCH_r17__sfnSchemeB
.
Definition MIMOParam_r17__sfnSchemePDSCH_r17__cond := (fun (_ : MIMOParam_r17__sfnSchemePDSCH_r17__Type) => True).
Lemma MIMOParam_r17__sfnSchemePDSCH_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMOParam_r17__sfnSchemePDSCH_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMOParam_r17__sfnSchemePDSCH_r17__nat__helper.

Definition MIMOParam_r17__sfnSchemePDSCH_r17__F1 t :=
  match t with
  | MIMOParam_r17__sfnSchemePDSCH_r17__sfnSchemeA => 0
  | MIMOParam_r17__sfnSchemePDSCH_r17__sfnSchemeB => 1
  end.
Definition MIMOParam_r17__sfnSchemePDSCH_r17__F2 n :=
  match n with
  | 0 => MIMOParam_r17__sfnSchemePDSCH_r17__sfnSchemeA
  | 1 => MIMOParam_r17__sfnSchemePDSCH_r17__sfnSchemeB
  | _ => MIMOParam_r17__sfnSchemePDSCH_r17__sfnSchemeA
  end.
Lemma MIMOParam_r17__sfnSchemePDSCH_r17__F1F2 : forall x : MIMOParam_r17__sfnSchemePDSCH_r17__Type, (MIMOParam_r17__sfnSchemePDSCH_r17__F1 x <= 1) /\ MIMOParam_r17__sfnSchemePDSCH_r17__F2 (MIMOParam_r17__sfnSchemePDSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMOParam_r17__sfnSchemePDSCH_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMOParam_r17__sfnSchemePDSCH_r17__F1 (MIMOParam_r17__sfnSchemePDSCH_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMOParam_r17__Type : Set :=
  make__MIMOParam_r17__Type {
    MIMOParam_r17__additionalPCI_ToAddModList_r17 : option MIMOParam_r17__additionalPCI_ToAddModList_r17__Type ;
    MIMOParam_r17__additionalPCI_ToReleaseList_r17 : option MIMOParam_r17__additionalPCI_ToReleaseList_r17__Type ;
    MIMOParam_r17__unifiedTCI_StateType_r17 : option MIMOParam_r17__unifiedTCI_StateType_r17__Type ;
    MIMOParam_r17__uplink_PowerControlToAddModList_r17 : option MIMOParam_r17__uplink_PowerControlToAddModList_r17__Type ;
    MIMOParam_r17__uplink_PowerControlToReleaseList_r17 : option MIMOParam_r17__uplink_PowerControlToReleaseList_r17__Type ;
    MIMOParam_r17__sfnSchemePDCCH_r17 : option MIMOParam_r17__sfnSchemePDCCH_r17__Type ;
    MIMOParam_r17__sfnSchemePDSCH_r17 : option MIMOParam_r17__sfnSchemePDSCH_r17__Type ;
}.
Definition MIMOParam_r17__list := (
 Opt MIMOParam_r17__additionalPCI_ToAddModList_r17__Type MIMOParam_r17__additionalPCI_ToAddModList_r17__cond ::
 Opt MIMOParam_r17__additionalPCI_ToReleaseList_r17__Type MIMOParam_r17__additionalPCI_ToReleaseList_r17__cond ::
 Opt MIMOParam_r17__unifiedTCI_StateType_r17__Type MIMOParam_r17__unifiedTCI_StateType_r17__cond ::
 Opt MIMOParam_r17__uplink_PowerControlToAddModList_r17__Type MIMOParam_r17__uplink_PowerControlToAddModList_r17__cond ::
 Opt MIMOParam_r17__uplink_PowerControlToReleaseList_r17__Type MIMOParam_r17__uplink_PowerControlToReleaseList_r17__cond ::
 Opt MIMOParam_r17__sfnSchemePDCCH_r17__Type MIMOParam_r17__sfnSchemePDCCH_r17__cond ::
 Opt MIMOParam_r17__sfnSchemePDSCH_r17__Type MIMOParam_r17__sfnSchemePDSCH_r17__cond ::
 nil).
Definition MIMOParam_r17__cond z := 
  opt_cond MIMOParam_r17__additionalPCI_ToAddModList_r17__cond (MIMOParam_r17__additionalPCI_ToAddModList_r17 z) /\
  opt_cond MIMOParam_r17__additionalPCI_ToReleaseList_r17__cond (MIMOParam_r17__additionalPCI_ToReleaseList_r17 z) /\
  opt_cond MIMOParam_r17__unifiedTCI_StateType_r17__cond (MIMOParam_r17__unifiedTCI_StateType_r17 z) /\
  opt_cond MIMOParam_r17__uplink_PowerControlToAddModList_r17__cond (MIMOParam_r17__uplink_PowerControlToAddModList_r17 z) /\
  opt_cond MIMOParam_r17__uplink_PowerControlToReleaseList_r17__cond (MIMOParam_r17__uplink_PowerControlToReleaseList_r17 z) /\
  opt_cond MIMOParam_r17__sfnSchemePDCCH_r17__cond (MIMOParam_r17__sfnSchemePDCCH_r17 z) /\
  opt_cond MIMOParam_r17__sfnSchemePDSCH_r17__cond (MIMOParam_r17__sfnSchemePDSCH_r17 z) /\
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
Definition MIMOParam_r17__additionalPCI_ToAddModList_r17__Format : T_Format MIMOParam_r17__additionalPCI_ToAddModList_r17__Type MIMOParam_r17__additionalPCI_ToAddModList_r17__cond := seq_of_format SSB_MTC_AdditionalPCI_r17__Format 1 maxNrofAdditionalPCI_r17 MIMOParam_r17__additionalPCI_ToAddModList_r17__helper1 MIMOParam_r17__additionalPCI_ToAddModList_r17__helper2.

Opaque MIMOParam_r17__additionalPCI_ToAddModList_r17__cond MIMOParam_r17__additionalPCI_ToAddModList_r17__Format.

Definition MIMOParam_r17__additionalPCI_ToReleaseList_r17__Format : T_Format MIMOParam_r17__additionalPCI_ToReleaseList_r17__Type MIMOParam_r17__additionalPCI_ToReleaseList_r17__cond := seq_of_format AdditionalPCIIndex_r17__Format 1 maxNrofAdditionalPCI_r17 MIMOParam_r17__additionalPCI_ToReleaseList_r17__helper1 MIMOParam_r17__additionalPCI_ToReleaseList_r17__helper2.

Opaque MIMOParam_r17__additionalPCI_ToReleaseList_r17__cond MIMOParam_r17__additionalPCI_ToReleaseList_r17__Format.

Definition MIMOParam_r17__unifiedTCI_StateType_r17__Format : T_Format MIMOParam_r17__unifiedTCI_StateType_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMOParam_r17__unifiedTCI_StateType_r17__nat__Format MIMOParam_r17__unifiedTCI_StateType_r17__F1 MIMOParam_r17__unifiedTCI_StateType_r17__F2 MIMOParam_r17__unifiedTCI_StateType_r17__F1F2 MIMOParam_r17__unifiedTCI_StateType_r17__F2F1.

Opaque MIMOParam_r17__unifiedTCI_StateType_r17__cond MIMOParam_r17__unifiedTCI_StateType_r17__Format.

Definition MIMOParam_r17__uplink_PowerControlToAddModList_r17__Format : T_Format MIMOParam_r17__uplink_PowerControlToAddModList_r17__Type MIMOParam_r17__uplink_PowerControlToAddModList_r17__cond := seq_of_format Uplink_powerControl_r17__Format 1 maxUL_TCI_r17 MIMOParam_r17__uplink_PowerControlToAddModList_r17__helper1 MIMOParam_r17__uplink_PowerControlToAddModList_r17__helper2.

Opaque MIMOParam_r17__uplink_PowerControlToAddModList_r17__cond MIMOParam_r17__uplink_PowerControlToAddModList_r17__Format.

Definition MIMOParam_r17__uplink_PowerControlToReleaseList_r17__Format : T_Format MIMOParam_r17__uplink_PowerControlToReleaseList_r17__Type MIMOParam_r17__uplink_PowerControlToReleaseList_r17__cond := seq_of_format Uplink_powerControlId_r17__Format 1 maxUL_TCI_r17 MIMOParam_r17__uplink_PowerControlToReleaseList_r17__helper1 MIMOParam_r17__uplink_PowerControlToReleaseList_r17__helper2.

Opaque MIMOParam_r17__uplink_PowerControlToReleaseList_r17__cond MIMOParam_r17__uplink_PowerControlToReleaseList_r17__Format.

Definition MIMOParam_r17__sfnSchemePDCCH_r17__Format : T_Format MIMOParam_r17__sfnSchemePDCCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMOParam_r17__sfnSchemePDCCH_r17__nat__Format MIMOParam_r17__sfnSchemePDCCH_r17__F1 MIMOParam_r17__sfnSchemePDCCH_r17__F2 MIMOParam_r17__sfnSchemePDCCH_r17__F1F2 MIMOParam_r17__sfnSchemePDCCH_r17__F2F1.

Opaque MIMOParam_r17__sfnSchemePDCCH_r17__cond MIMOParam_r17__sfnSchemePDCCH_r17__Format.

Definition MIMOParam_r17__sfnSchemePDSCH_r17__Format : T_Format MIMOParam_r17__sfnSchemePDSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMOParam_r17__sfnSchemePDSCH_r17__nat__Format MIMOParam_r17__sfnSchemePDSCH_r17__F1 MIMOParam_r17__sfnSchemePDSCH_r17__F2 MIMOParam_r17__sfnSchemePDSCH_r17__F1F2 MIMOParam_r17__sfnSchemePDSCH_r17__F2F1.

Opaque MIMOParam_r17__sfnSchemePDSCH_r17__cond MIMOParam_r17__sfnSchemePDSCH_r17__Format.


Definition MIMOParam_r17__Format_Type := Eval cbn in seq_format_prod MIMOParam_r17__list.
Definition MIMOParam_r17__Format_list : MIMOParam_r17__Format_Type :=
  (MIMOParam_r17__additionalPCI_ToAddModList_r17__Format, (MIMOParam_r17__additionalPCI_ToReleaseList_r17__Format, (MIMOParam_r17__unifiedTCI_StateType_r17__Format, (MIMOParam_r17__uplink_PowerControlToAddModList_r17__Format, (MIMOParam_r17__uplink_PowerControlToReleaseList_r17__Format, (MIMOParam_r17__sfnSchemePDCCH_r17__Format, (MIMOParam_r17__sfnSchemePDSCH_r17__Format, unit_format))))))).
Definition MIMOParam_r17__list__Format := (*Eval compute in *) seq_format MIMOParam_r17__list MIMOParam_r17__Format_list.
Definition MIMOParam_r17__F1 z :=
  (MIMOParam_r17__additionalPCI_ToAddModList_r17 z, (MIMOParam_r17__additionalPCI_ToReleaseList_r17 z, (MIMOParam_r17__unifiedTCI_StateType_r17 z, (MIMOParam_r17__uplink_PowerControlToAddModList_r17 z, (MIMOParam_r17__uplink_PowerControlToReleaseList_r17 z, (MIMOParam_r17__sfnSchemePDCCH_r17 z, (MIMOParam_r17__sfnSchemePDSCH_r17 z, tt))))))).
Definition MIMOParam_r17__F2 (y : seq_type MIMOParam_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__MIMOParam_r17__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma MIMOParam_r17__F1F2_cond (z : MIMOParam_r17__Type)
  : MIMOParam_r17__cond z ->
  (seq_cond MIMOParam_r17__list (MIMOParam_r17__F1 z)).
intro H. unfold MIMOParam_r17__cond in H. simpl. auto. Qed.
Lemma MIMOParam_r17__F1F2_cond2 (z : MIMOParam_r17__Type)
 : MIMOParam_r17__F2 (MIMOParam_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMOParam_r17__F2F1_cond (y : seq_type MIMOParam_r17__list)
  : seq_cond MIMOParam_r17__list y ->
 (MIMOParam_r17__cond (MIMOParam_r17__F2 y)) /\  MIMOParam_r17__F1 (MIMOParam_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMOParam_r17__cond. simpl in *. auto.
 - simpl. unfold MIMOParam_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMOParam_r17__Format : T_Format MIMOParam_r17__Type MIMOParam_r17__cond :=
        proj2_format  MIMOParam_r17__cond MIMOParam_r17__list__Format
    MIMOParam_r17__F1 MIMOParam_r17__F2 MIMOParam_r17__F1F2_cond  MIMOParam_r17__F1F2_cond2 MIMOParam_r17__F2F1_cond.
Opaque MIMOParam_r17__cond MIMOParam_r17__Format.

