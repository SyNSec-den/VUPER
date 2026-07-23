Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Type : Set :=
 | MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos0
 | MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos1
 | MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos3
.
Definition MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__cond := (fun (_ : MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Type) => True).
Lemma MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__nat__helper.

Definition MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F1 t :=
  match t with
  | MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos0 => 0
  | MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos1 => 1
  | MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos3 => 2
  end.
Definition MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F2 n :=
  match n with
  | 0 => MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos0
  | 1 => MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos1
  | 2 => MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos3
  | _ => MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__pos0
  end.
Lemma MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F1F2 : forall x : MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Type, (MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F1 x <= 2) /\ MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F2 (MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F1 x) = x. imp_solve. Qed.
Lemma MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F2F1 : forall (y : nat) (H : y <= 2), MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F1 (MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Type : Set :=
 | MsgA_DMRS_Config_r16__msgA_MaxLength_r16__len2
.
Definition MsgA_DMRS_Config_r16__msgA_MaxLength_r16__cond := (fun (_ : MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Type) => True).
Lemma MsgA_DMRS_Config_r16__msgA_MaxLength_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MsgA_DMRS_Config_r16__msgA_MaxLength_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MsgA_DMRS_Config_r16__msgA_MaxLength_r16__nat__helper.

Definition MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F1 t :=
  match t with
  | MsgA_DMRS_Config_r16__msgA_MaxLength_r16__len2 => 0
  end.
Definition MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F2 n :=
  match n with
  | 0 => MsgA_DMRS_Config_r16__msgA_MaxLength_r16__len2
  | _ => MsgA_DMRS_Config_r16__msgA_MaxLength_r16__len2
  end.
Lemma MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F1F2 : forall x : MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Type, (MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F1 x <= 0) /\ MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F2 (MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F1 x) = x. imp_solve. Qed.
Lemma MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F2F1 : forall (y : nat) (H : y <= 0), MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F1 (MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F2 y) = y. enum_solve H y. Qed.

Lemma MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__Type := Z.
Definition MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__cond := (fun z => (0 <= z <= 1)%Z).
Lemma MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__Type := Z.
Definition MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__cond := (fun z => (0 <= z <= 1)%Z).
Lemma MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__Type := Z.
Definition MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__cond := (fun z => (0 <= z <= 65535)%Z).
Lemma MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__Type := Z.
Definition MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__cond := (fun z => (0 <= z <= 65535)%Z).
Record MsgA_DMRS_Config_r16__Type : Set :=
  make__MsgA_DMRS_Config_r16__Type {
    MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16 : option MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Type ;
    MsgA_DMRS_Config_r16__msgA_MaxLength_r16 : option MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Type ;
    MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16 : option Z ;
    MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16 : option Z ;
    MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16 : option Z ;
    MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16 : option Z ;
}.
Definition MsgA_DMRS_Config_r16__list := (
 Opt MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Type MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__cond ::
 Opt MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Type MsgA_DMRS_Config_r16__msgA_MaxLength_r16__cond ::
 Opt Z MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__cond ::
 Opt Z MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__cond ::
 Opt Z MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__cond ::
 Opt Z MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__cond ::
 nil).
Definition MsgA_DMRS_Config_r16__cond z := 
  opt_cond MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__cond (MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16 z) /\
  opt_cond MsgA_DMRS_Config_r16__msgA_MaxLength_r16__cond (MsgA_DMRS_Config_r16__msgA_MaxLength_r16 z) /\
  opt_cond MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__cond (MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16 z) /\
  opt_cond MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__cond (MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16 z) /\
  opt_cond MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__cond (MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16 z) /\
  opt_cond MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__cond (MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16 z) /\
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
Definition MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Format : T_Format MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__nat__Format MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F1 MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F2 MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F1F2 MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__F2F1.

Opaque MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__cond MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Format.

Definition MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Format : T_Format MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MsgA_DMRS_Config_r16__msgA_MaxLength_r16__nat__Format MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F1 MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F2 MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F1F2 MsgA_DMRS_Config_r16__msgA_MaxLength_r16__F2F1.

Opaque MsgA_DMRS_Config_r16__msgA_MaxLength_r16__cond MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Format.

Definition MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__Format : T_Format Z MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__cond :=
 ranged_int_format (0) (1) MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__helper1 MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__helper2.

Opaque MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__cond MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__Format.

Definition MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__Format : T_Format Z MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__cond :=
 ranged_int_format (0) (1) MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__helper1 MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__helper2.

Opaque MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__cond MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__Format.

Definition MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__Format : T_Format Z MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__cond :=
 ranged_int_format (0) (65535) MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__helper1 MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__helper2.

Opaque MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__cond MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__Format.

Definition MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__Format : T_Format Z MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__cond :=
 ranged_int_format (0) (65535) MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__helper1 MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__helper2.

Opaque MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__cond MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__Format.


Definition MsgA_DMRS_Config_r16__Format_Type := Eval cbn in seq_format_prod MsgA_DMRS_Config_r16__list.
Definition MsgA_DMRS_Config_r16__Format_list : MsgA_DMRS_Config_r16__Format_Type :=
  (MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16__Format, (MsgA_DMRS_Config_r16__msgA_MaxLength_r16__Format, (MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16__Format, (MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16__Format, (MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16__Format, (MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16__Format, unit_format)))))).
Definition MsgA_DMRS_Config_r16__list__Format := (*Eval compute in *) seq_format MsgA_DMRS_Config_r16__list MsgA_DMRS_Config_r16__Format_list.
Definition MsgA_DMRS_Config_r16__F1 z :=
  (MsgA_DMRS_Config_r16__msgA_DMRS_AdditionalPosition_r16 z, (MsgA_DMRS_Config_r16__msgA_MaxLength_r16 z, (MsgA_DMRS_Config_r16__msgA_PUSCH_DMRS_CDM_Group_r16 z, (MsgA_DMRS_Config_r16__msgA_PUSCH_NrofPorts_r16 z, (MsgA_DMRS_Config_r16__msgA_ScramblingID0_r16 z, (MsgA_DMRS_Config_r16__msgA_ScramblingID1_r16 z, tt)))))).
Definition MsgA_DMRS_Config_r16__F2 (y : seq_type MsgA_DMRS_Config_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__MsgA_DMRS_Config_r16__Type i0 i1 i2 i3 i4 i5
  end.
Lemma MsgA_DMRS_Config_r16__F1F2_cond (z : MsgA_DMRS_Config_r16__Type)
  : MsgA_DMRS_Config_r16__cond z ->
  (seq_cond MsgA_DMRS_Config_r16__list (MsgA_DMRS_Config_r16__F1 z)).
intro H. unfold MsgA_DMRS_Config_r16__cond in H. simpl. auto. Qed.
Lemma MsgA_DMRS_Config_r16__F1F2_cond2 (z : MsgA_DMRS_Config_r16__Type)
 : MsgA_DMRS_Config_r16__F2 (MsgA_DMRS_Config_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MsgA_DMRS_Config_r16__F2F1_cond (y : seq_type MsgA_DMRS_Config_r16__list)
  : seq_cond MsgA_DMRS_Config_r16__list y ->
 (MsgA_DMRS_Config_r16__cond (MsgA_DMRS_Config_r16__F2 y)) /\  MsgA_DMRS_Config_r16__F1 (MsgA_DMRS_Config_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MsgA_DMRS_Config_r16__cond. simpl in *. auto.
 - simpl. unfold MsgA_DMRS_Config_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MsgA_DMRS_Config_r16__Format : T_Format MsgA_DMRS_Config_r16__Type MsgA_DMRS_Config_r16__cond :=
        proj2_format  MsgA_DMRS_Config_r16__cond MsgA_DMRS_Config_r16__list__Format
    MsgA_DMRS_Config_r16__F1 MsgA_DMRS_Config_r16__F2 MsgA_DMRS_Config_r16__F1F2_cond  MsgA_DMRS_Config_r16__F1F2_cond2 MsgA_DMRS_Config_r16__F2F1_cond.
Opaque MsgA_DMRS_Config_r16__cond MsgA_DMRS_Config_r16__Format.

