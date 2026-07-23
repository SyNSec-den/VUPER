Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.InterFreqNeighHSDN_CellList_r17.

Opaque InterFreqNeighHSDN_CellList_r17__cond InterFreqNeighHSDN_CellList_r17__Format.

Inductive InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Type : Set :=
 | InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__true
.
Definition InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__cond := (fun (_ : InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Type) => True).
Lemma InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__nat__helper.

Definition InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F1 t :=
  match t with
  | InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__true => 0
  end.
Definition InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F2 n :=
  match n with
  | 0 => InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__true
  | _ => InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__true
  end.
Lemma InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F1F2 : forall x : InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Type, (InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F1 x <= 0) /\ InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F2 (InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F1 x) = x. imp_solve. Qed.
Lemma InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F2F1 : forall (y : nat) (H : y <= 0), InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F1 (InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F2 y) = y. enum_solve H y. Qed.

Inductive InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Type : Set :=
 | InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__true
.
Definition InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__cond := (fun (_ : InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Type) => True).
Lemma InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__nat__helper.

Definition InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F1 t :=
  match t with
  | InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__true => 0
  end.
Definition InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F2 n :=
  match n with
  | 0 => InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__true
  | _ => InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__true
  end.
Lemma InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F1F2 : forall x : InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Type, (InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F1 x <= 0) /\ InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F2 (InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F1 x) = x. imp_solve. Qed.
Lemma InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F2F1 : forall (y : nat) (H : y <= 0), InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F1 (InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SSB_PositionQCL_Relation_r17.

Opaque SSB_PositionQCL_Relation_r17__cond SSB_PositionQCL_Relation_r17__Format.

Require Import NR.InterFreqNeighCellList_v1710.

Opaque InterFreqNeighCellList_v1710__cond InterFreqNeighCellList_v1710__Format.

Record InterFreqCarrierFreqInfo_v1700__Type : Set :=
  make__InterFreqCarrierFreqInfo_v1700__Type {
    InterFreqCarrierFreqInfo_v1700__interFreqNeighHSDN_CellList_r17 : option InterFreqNeighHSDN_CellList_r17__Type ;
    InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17 : option InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Type ;
    InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17 : option InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Type ;
    InterFreqCarrierFreqInfo_v1700__ssb_PositionQCL_Common_r17 : option SSB_PositionQCL_Relation_r17__Type ;
    InterFreqCarrierFreqInfo_v1700__interFreqNeighCellList_v1710 : option InterFreqNeighCellList_v1710__Type ;
}.
Definition InterFreqCarrierFreqInfo_v1700__list := (
 Opt InterFreqNeighHSDN_CellList_r17__Type InterFreqNeighHSDN_CellList_r17__cond ::
 Opt InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Type InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__cond ::
 Opt InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Type InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__cond ::
 Opt SSB_PositionQCL_Relation_r17__Type SSB_PositionQCL_Relation_r17__cond ::
 Opt InterFreqNeighCellList_v1710__Type InterFreqNeighCellList_v1710__cond ::
 nil).
Definition InterFreqCarrierFreqInfo_v1700__cond z := 
  opt_cond InterFreqNeighHSDN_CellList_r17__cond (InterFreqCarrierFreqInfo_v1700__interFreqNeighHSDN_CellList_r17 z) /\
  opt_cond InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__cond (InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17 z) /\
  opt_cond InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__cond (InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17 z) /\
  opt_cond SSB_PositionQCL_Relation_r17__cond (InterFreqCarrierFreqInfo_v1700__ssb_PositionQCL_Common_r17 z) /\
  opt_cond InterFreqNeighCellList_v1710__cond (InterFreqCarrierFreqInfo_v1700__interFreqNeighCellList_v1710 z) /\
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
Definition InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Format : T_Format InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__nat__Format InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F1 InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F2 InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F1F2 InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__F2F1.

Opaque InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__cond InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Format.

Definition InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Format : T_Format InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__nat__Format InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F1 InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F2 InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F1F2 InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__F2F1.

Opaque InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__cond InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Format.


Definition InterFreqCarrierFreqInfo_v1700__Format_Type := Eval cbn in seq_format_prod InterFreqCarrierFreqInfo_v1700__list.
Definition InterFreqCarrierFreqInfo_v1700__Format_list : InterFreqCarrierFreqInfo_v1700__Format_Type :=
  (InterFreqNeighHSDN_CellList_r17__Format, (InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17__Format, (InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17__Format, (SSB_PositionQCL_Relation_r17__Format, (InterFreqNeighCellList_v1710__Format, unit_format))))).
Definition InterFreqCarrierFreqInfo_v1700__list__Format := (*Eval compute in *) seq_format InterFreqCarrierFreqInfo_v1700__list InterFreqCarrierFreqInfo_v1700__Format_list.
Definition InterFreqCarrierFreqInfo_v1700__F1 z :=
  (InterFreqCarrierFreqInfo_v1700__interFreqNeighHSDN_CellList_r17 z, (InterFreqCarrierFreqInfo_v1700__highSpeedMeasInterFreq_r17 z, (InterFreqCarrierFreqInfo_v1700__redCapAccessAllowed_r17 z, (InterFreqCarrierFreqInfo_v1700__ssb_PositionQCL_Common_r17 z, (InterFreqCarrierFreqInfo_v1700__interFreqNeighCellList_v1710 z, tt))))).
Definition InterFreqCarrierFreqInfo_v1700__F2 (y : seq_type InterFreqCarrierFreqInfo_v1700__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__InterFreqCarrierFreqInfo_v1700__Type i0 i1 i2 i3 i4
  end.
Lemma InterFreqCarrierFreqInfo_v1700__F1F2_cond (z : InterFreqCarrierFreqInfo_v1700__Type)
  : InterFreqCarrierFreqInfo_v1700__cond z ->
  (seq_cond InterFreqCarrierFreqInfo_v1700__list (InterFreqCarrierFreqInfo_v1700__F1 z)).
intro H. unfold InterFreqCarrierFreqInfo_v1700__cond in H. simpl. auto. Qed.
Lemma InterFreqCarrierFreqInfo_v1700__F1F2_cond2 (z : InterFreqCarrierFreqInfo_v1700__Type)
 : InterFreqCarrierFreqInfo_v1700__F2 (InterFreqCarrierFreqInfo_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma InterFreqCarrierFreqInfo_v1700__F2F1_cond (y : seq_type InterFreqCarrierFreqInfo_v1700__list)
  : seq_cond InterFreqCarrierFreqInfo_v1700__list y ->
 (InterFreqCarrierFreqInfo_v1700__cond (InterFreqCarrierFreqInfo_v1700__F2 y)) /\  InterFreqCarrierFreqInfo_v1700__F1 (InterFreqCarrierFreqInfo_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold InterFreqCarrierFreqInfo_v1700__cond. simpl in *. auto.
 - simpl. unfold InterFreqCarrierFreqInfo_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition InterFreqCarrierFreqInfo_v1700__Format : T_Format InterFreqCarrierFreqInfo_v1700__Type InterFreqCarrierFreqInfo_v1700__cond :=
        proj2_format  InterFreqCarrierFreqInfo_v1700__cond InterFreqCarrierFreqInfo_v1700__list__Format
    InterFreqCarrierFreqInfo_v1700__F1 InterFreqCarrierFreqInfo_v1700__F2 InterFreqCarrierFreqInfo_v1700__F1F2_cond  InterFreqCarrierFreqInfo_v1700__F1F2_cond2 InterFreqCarrierFreqInfo_v1700__F2F1_cond.
Opaque InterFreqCarrierFreqInfo_v1700__cond InterFreqCarrierFreqInfo_v1700__Format.

