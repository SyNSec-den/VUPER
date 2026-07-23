Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Inductive CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Type : Set :=
 | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size24
 | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size48
 | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size96
 | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size192
 | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size264
.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__cond := (fun (_ : CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Type) => True).
Lemma CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__nat__helper.

Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F1 t :=
  match t with
  | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size24 => 0
  | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size48 => 1
  | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size96 => 2
  | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size192 => 3
  | CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size264 => 4
  end.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F2 n :=
  match n with
  | 0 => CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size24
  | 1 => CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size48
  | 2 => CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size96
  | 3 => CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size192
  | 4 => CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size264
  | _ => CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__size24
  end.
Lemma CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F1F2 : forall x : CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Type, (CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F1 x <= 4) /\ CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F2 (CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F1 x) = x. imp_solve. Qed.
Lemma CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F2F1 : forall (y : nat) (H : y <= 4), CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F1 (CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F2 y) = y. enum_solve H y. Qed.

Lemma CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__helper1 : (0 <= 2169)%Z.  lia. Qed.
Lemma CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__helper2 : to_bit_sz (Z.to_nat (2169 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2169 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__Type := Z.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__cond := (fun z => (0 <= z <= 2169)%Z).
Record CSI_RS_CellMobility__csi_rs_MeasurementBW__Type : Set :=
  make__CSI_RS_CellMobility__csi_rs_MeasurementBW__Type {
    CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs : CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Type ;
    CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB : Z ;
}.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__list := (
 Nor CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Type CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__cond ::
 Nor Z CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__cond ::
 nil).
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__cond z := 
  CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__cond (CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs z) /\
  CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__cond (CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB z) /\
  True.

Inductive CSI_RS_CellMobility__density__Type : Set :=
 | CSI_RS_CellMobility__density__d1
 | CSI_RS_CellMobility__density__d3
.
Definition CSI_RS_CellMobility__density__cond := (fun (_ : CSI_RS_CellMobility__density__Type) => True).
Lemma CSI_RS_CellMobility__density__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_RS_CellMobility__density__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_RS_CellMobility__density__nat__helper.

Definition CSI_RS_CellMobility__density__F1 t :=
  match t with
  | CSI_RS_CellMobility__density__d1 => 0
  | CSI_RS_CellMobility__density__d3 => 1
  end.
Definition CSI_RS_CellMobility__density__F2 n :=
  match n with
  | 0 => CSI_RS_CellMobility__density__d1
  | 1 => CSI_RS_CellMobility__density__d3
  | _ => CSI_RS_CellMobility__density__d1
  end.
Lemma CSI_RS_CellMobility__density__F1F2 : forall x : CSI_RS_CellMobility__density__Type, (CSI_RS_CellMobility__density__F1 x <= 1) /\ CSI_RS_CellMobility__density__F2 (CSI_RS_CellMobility__density__F1 x) = x. imp_solve. Qed.
Lemma CSI_RS_CellMobility__density__F2F1 : forall (y : nat) (H : y <= 1), CSI_RS_CellMobility__density__F1 (CSI_RS_CellMobility__density__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CSI_RS_Resource_Mobility.

Opaque CSI_RS_Resource_Mobility__cond CSI_RS_Resource_Mobility__Format.

Definition CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__Type := list CSI_RS_Resource_Mobility__Type.

Lemma CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesRRM)%Z. unfold maxNrofCSI_RS_ResourcesRRM.
 lia. Qed.
Lemma CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesRRM - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesRRM - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__cond (z : CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesRRM)%Z /\ (list_and CSI_RS_Resource_Mobility__cond z) .

Record CSI_RS_CellMobility__Type : Set :=
  make__CSI_RS_CellMobility__Type {
    CSI_RS_CellMobility__cellId : PhysCellId__Type ;
    CSI_RS_CellMobility__csi_rs_MeasurementBW : CSI_RS_CellMobility__csi_rs_MeasurementBW__Type ;
    CSI_RS_CellMobility__density : option CSI_RS_CellMobility__density__Type ;
    CSI_RS_CellMobility__csi_rs_ResourceList_Mobility : CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__Type ;
}.
Definition CSI_RS_CellMobility__list := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor CSI_RS_CellMobility__csi_rs_MeasurementBW__Type CSI_RS_CellMobility__csi_rs_MeasurementBW__cond ::
 Opt CSI_RS_CellMobility__density__Type CSI_RS_CellMobility__density__cond ::
 Nor CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__Type CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__cond ::
 nil).
Definition CSI_RS_CellMobility__cond z := 
  PhysCellId__cond (CSI_RS_CellMobility__cellId z) /\
  CSI_RS_CellMobility__csi_rs_MeasurementBW__cond (CSI_RS_CellMobility__csi_rs_MeasurementBW z) /\
  opt_cond CSI_RS_CellMobility__density__cond (CSI_RS_CellMobility__density z) /\
  CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__cond (CSI_RS_CellMobility__csi_rs_ResourceList_Mobility z) /\
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
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Format : T_Format CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__nat__Format CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F1 CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F2 CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F1F2 CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__F2F1.

Opaque CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__cond CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Format.

Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__Format : T_Format Z CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__cond :=
 ranged_int_format (0) (2169) CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__helper1 CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__helper2.

Opaque CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__cond CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__Format.


Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__Format_Type := Eval cbn in seq_format_prod CSI_RS_CellMobility__csi_rs_MeasurementBW__list.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__Format_list : CSI_RS_CellMobility__csi_rs_MeasurementBW__Format_Type :=
  (CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs__Format, (CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB__Format, unit_format)).
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__list__Format := (*Eval compute in *) seq_format CSI_RS_CellMobility__csi_rs_MeasurementBW__list CSI_RS_CellMobility__csi_rs_MeasurementBW__Format_list.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__F1 z :=
  (CSI_RS_CellMobility__csi_rs_MeasurementBW__nrofPRBs z, (CSI_RS_CellMobility__csi_rs_MeasurementBW__startPRB z, tt)).
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__F2 (y : seq_type CSI_RS_CellMobility__csi_rs_MeasurementBW__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_RS_CellMobility__csi_rs_MeasurementBW__Type i0 i1
  end.
Lemma CSI_RS_CellMobility__csi_rs_MeasurementBW__F1F2_cond (z : CSI_RS_CellMobility__csi_rs_MeasurementBW__Type)
  : CSI_RS_CellMobility__csi_rs_MeasurementBW__cond z ->
  (seq_cond CSI_RS_CellMobility__csi_rs_MeasurementBW__list (CSI_RS_CellMobility__csi_rs_MeasurementBW__F1 z)).
intro H. unfold CSI_RS_CellMobility__csi_rs_MeasurementBW__cond in H. simpl. auto. Qed.
Lemma CSI_RS_CellMobility__csi_rs_MeasurementBW__F1F2_cond2 (z : CSI_RS_CellMobility__csi_rs_MeasurementBW__Type)
 : CSI_RS_CellMobility__csi_rs_MeasurementBW__F2 (CSI_RS_CellMobility__csi_rs_MeasurementBW__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_RS_CellMobility__csi_rs_MeasurementBW__F2F1_cond (y : seq_type CSI_RS_CellMobility__csi_rs_MeasurementBW__list)
  : seq_cond CSI_RS_CellMobility__csi_rs_MeasurementBW__list y ->
 (CSI_RS_CellMobility__csi_rs_MeasurementBW__cond (CSI_RS_CellMobility__csi_rs_MeasurementBW__F2 y)) /\  CSI_RS_CellMobility__csi_rs_MeasurementBW__F1 (CSI_RS_CellMobility__csi_rs_MeasurementBW__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_RS_CellMobility__csi_rs_MeasurementBW__cond. simpl in *. auto.
 - simpl. unfold CSI_RS_CellMobility__csi_rs_MeasurementBW__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_RS_CellMobility__csi_rs_MeasurementBW__Format : T_Format CSI_RS_CellMobility__csi_rs_MeasurementBW__Type CSI_RS_CellMobility__csi_rs_MeasurementBW__cond :=
        proj2_format  CSI_RS_CellMobility__csi_rs_MeasurementBW__cond CSI_RS_CellMobility__csi_rs_MeasurementBW__list__Format
    CSI_RS_CellMobility__csi_rs_MeasurementBW__F1 CSI_RS_CellMobility__csi_rs_MeasurementBW__F2 CSI_RS_CellMobility__csi_rs_MeasurementBW__F1F2_cond  CSI_RS_CellMobility__csi_rs_MeasurementBW__F1F2_cond2 CSI_RS_CellMobility__csi_rs_MeasurementBW__F2F1_cond.
Opaque CSI_RS_CellMobility__csi_rs_MeasurementBW__cond CSI_RS_CellMobility__csi_rs_MeasurementBW__Format.

Definition CSI_RS_CellMobility__density__Format : T_Format CSI_RS_CellMobility__density__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_RS_CellMobility__density__nat__Format CSI_RS_CellMobility__density__F1 CSI_RS_CellMobility__density__F2 CSI_RS_CellMobility__density__F1F2 CSI_RS_CellMobility__density__F2F1.

Opaque CSI_RS_CellMobility__density__cond CSI_RS_CellMobility__density__Format.

Definition CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__Format : T_Format CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__Type CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__cond := seq_of_format CSI_RS_Resource_Mobility__Format 1 maxNrofCSI_RS_ResourcesRRM CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__helper1 CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__helper2.

Opaque CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__cond CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__Format.


Definition CSI_RS_CellMobility__Format_Type := Eval cbn in seq_format_prod CSI_RS_CellMobility__list.
Definition CSI_RS_CellMobility__Format_list : CSI_RS_CellMobility__Format_Type :=
  (PhysCellId__Format, (CSI_RS_CellMobility__csi_rs_MeasurementBW__Format, (CSI_RS_CellMobility__density__Format, (CSI_RS_CellMobility__csi_rs_ResourceList_Mobility__Format, unit_format)))).
Definition CSI_RS_CellMobility__list__Format := (*Eval compute in *) seq_format CSI_RS_CellMobility__list CSI_RS_CellMobility__Format_list.
Definition CSI_RS_CellMobility__F1 z :=
  (CSI_RS_CellMobility__cellId z, (CSI_RS_CellMobility__csi_rs_MeasurementBW z, (CSI_RS_CellMobility__density z, (CSI_RS_CellMobility__csi_rs_ResourceList_Mobility z, tt)))).
Definition CSI_RS_CellMobility__F2 (y : seq_type CSI_RS_CellMobility__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CSI_RS_CellMobility__Type i0 i1 i2 i3
  end.
Lemma CSI_RS_CellMobility__F1F2_cond (z : CSI_RS_CellMobility__Type)
  : CSI_RS_CellMobility__cond z ->
  (seq_cond CSI_RS_CellMobility__list (CSI_RS_CellMobility__F1 z)).
intro H. unfold CSI_RS_CellMobility__cond in H. simpl. auto. Qed.
Lemma CSI_RS_CellMobility__F1F2_cond2 (z : CSI_RS_CellMobility__Type)
 : CSI_RS_CellMobility__F2 (CSI_RS_CellMobility__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_RS_CellMobility__F2F1_cond (y : seq_type CSI_RS_CellMobility__list)
  : seq_cond CSI_RS_CellMobility__list y ->
 (CSI_RS_CellMobility__cond (CSI_RS_CellMobility__F2 y)) /\  CSI_RS_CellMobility__F1 (CSI_RS_CellMobility__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_RS_CellMobility__cond. simpl in *. auto.
 - simpl. unfold CSI_RS_CellMobility__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_RS_CellMobility__Format : T_Format CSI_RS_CellMobility__Type CSI_RS_CellMobility__cond :=
        proj2_format  CSI_RS_CellMobility__cond CSI_RS_CellMobility__list__Format
    CSI_RS_CellMobility__F1 CSI_RS_CellMobility__F2 CSI_RS_CellMobility__F1F2_cond  CSI_RS_CellMobility__F1F2_cond2 CSI_RS_CellMobility__F2F1_cond.
Opaque CSI_RS_CellMobility__cond CSI_RS_CellMobility__Format.

