Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Require Import NR.EUTRA_AllowedMeasBandwidth.

Opaque EUTRA_AllowedMeasBandwidth__cond EUTRA_AllowedMeasBandwidth__Format.

Require Import NR.EUTRA_CellIndexList.

Opaque EUTRA_CellIndexList__cond EUTRA_CellIndexList__Format.

Require Import NR.EUTRA_Cell.

Opaque EUTRA_Cell__cond EUTRA_Cell__Format.

Definition MeasObjectEUTRA__cellsToAddModListEUTRAN__Type := list EUTRA_Cell__Type.

Lemma MeasObjectEUTRA__cellsToAddModListEUTRAN__helper1 : (0 <= 1 <= maxCellMeasEUTRA)%Z. unfold maxCellMeasEUTRA.
 lia. Qed.
Lemma MeasObjectEUTRA__cellsToAddModListEUTRAN__helper2 : to_bit_sz (Z.to_nat (maxCellMeasEUTRA - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellMeasEUTRA - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasObjectEUTRA__cellsToAddModListEUTRAN__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasObjectEUTRA__cellsToAddModListEUTRAN__cond (z : MeasObjectEUTRA__cellsToAddModListEUTRAN__Type) :=  (1 <= Z.of_nat (length z) <= maxCellMeasEUTRA)%Z /\ (list_and EUTRA_Cell__cond z) .

Require Import NR.EUTRA_CellIndexList.

Opaque EUTRA_CellIndexList__cond EUTRA_CellIndexList__Format.

Require Import NR.EUTRA_ExcludedCell.

Opaque EUTRA_ExcludedCell__cond EUTRA_ExcludedCell__Format.

Definition MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__Type := list EUTRA_ExcludedCell__Type.

Lemma MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__helper1 : (0 <= 1 <= maxCellMeasEUTRA)%Z. unfold maxCellMeasEUTRA.
 lia. Qed.
Lemma MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__helper2 : to_bit_sz (Z.to_nat (maxCellMeasEUTRA - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellMeasEUTRA - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__cond (z : MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__Type) :=  (1 <= Z.of_nat (length z) <= maxCellMeasEUTRA)%Z /\ (list_and EUTRA_ExcludedCell__cond z) .

Require Import NR.EUTRA_PresenceAntennaPort1.

Opaque EUTRA_PresenceAntennaPort1__cond EUTRA_PresenceAntennaPort1__Format.

Require Import NR.EUTRA_Q_OffsetRange.

Opaque EUTRA_Q_OffsetRange__cond EUTRA_Q_OffsetRange__Format.

Require Import NR.MeasGapId_r17.

Opaque MeasGapId_r17__cond MeasGapId_r17__Format.

Record MeasObjectEUTRA__ext0O__Type : Set :=
  make__MeasObjectEUTRA__ext0O__Type {
    MeasObjectEUTRA__ext0O__associatedMeasGap_r17 : option MeasGapId_r17__Type ;
}.
Definition MeasObjectEUTRA__ext0O__list := (
 Opt MeasGapId_r17__Type MeasGapId_r17__cond ::
 nil).
Definition MeasObjectEUTRA__ext0O__cond z := 
  opt_cond MeasGapId_r17__cond (MeasObjectEUTRA__ext0O__associatedMeasGap_r17 z) /\
  True.

Definition MeasObjectEUTRA__ext0__Type := MeasObjectEUTRA__ext0O__Type.
Definition MeasObjectEUTRA__ext0__cond := MeasObjectEUTRA__ext0O__cond.

Record MeasObjectEUTRA__Type : Set :=
  make__MeasObjectEUTRA__Type {
    MeasObjectEUTRA__carrierFreq : ARFCN_ValueEUTRA__Type ;
    MeasObjectEUTRA__allowedMeasBandwidth : EUTRA_AllowedMeasBandwidth__Type ;
    MeasObjectEUTRA__cellsToRemoveListEUTRAN : option EUTRA_CellIndexList__Type ;
    MeasObjectEUTRA__cellsToAddModListEUTRAN : option MeasObjectEUTRA__cellsToAddModListEUTRAN__Type ;
    MeasObjectEUTRA__excludedCellsToRemoveListEUTRAN : option EUTRA_CellIndexList__Type ;
    MeasObjectEUTRA__excludedCellsToAddModListEUTRAN : option MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__Type ;
    MeasObjectEUTRA__eutra_PresenceAntennaPort1 : EUTRA_PresenceAntennaPort1__Type ;
    MeasObjectEUTRA__eutra_Q_OffsetRange : option EUTRA_Q_OffsetRange__Type ;
    MeasObjectEUTRA__widebandRSRQ_Meas : bool ;
    MeasObjectEUTRA__ext0 : option MeasObjectEUTRA__ext0__Type ;
}.
Definition MeasObjectEUTRA__root_list : list seq_elem := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Nor EUTRA_AllowedMeasBandwidth__Type EUTRA_AllowedMeasBandwidth__cond ::
 Opt EUTRA_CellIndexList__Type EUTRA_CellIndexList__cond ::
 Opt MeasObjectEUTRA__cellsToAddModListEUTRAN__Type MeasObjectEUTRA__cellsToAddModListEUTRAN__cond ::
 Opt EUTRA_CellIndexList__Type EUTRA_CellIndexList__cond ::
 Opt MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__Type MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__cond ::
 Nor EUTRA_PresenceAntennaPort1__Type EUTRA_PresenceAntennaPort1__cond ::
 Opt EUTRA_Q_OffsetRange__Type EUTRA_Q_OffsetRange__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition MeasObjectEUTRA__ext_list : list typ := (
  typ_cons MeasObjectEUTRA__ext0__Type MeasObjectEUTRA__ext0__cond ::
  nil).
Definition MeasObjectEUTRA__cond (z : MeasObjectEUTRA__Type) := 
(  ARFCN_ValueEUTRA__cond (MeasObjectEUTRA__carrierFreq z) /\
  EUTRA_AllowedMeasBandwidth__cond (MeasObjectEUTRA__allowedMeasBandwidth z) /\
  opt_cond EUTRA_CellIndexList__cond (MeasObjectEUTRA__cellsToRemoveListEUTRAN z) /\
  opt_cond MeasObjectEUTRA__cellsToAddModListEUTRAN__cond (MeasObjectEUTRA__cellsToAddModListEUTRAN z) /\
  opt_cond EUTRA_CellIndexList__cond (MeasObjectEUTRA__excludedCellsToRemoveListEUTRAN z) /\
  opt_cond MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__cond (MeasObjectEUTRA__excludedCellsToAddModListEUTRAN z) /\
  EUTRA_PresenceAntennaPort1__cond (MeasObjectEUTRA__eutra_PresenceAntennaPort1 z) /\
  opt_cond EUTRA_Q_OffsetRange__cond (MeasObjectEUTRA__eutra_Q_OffsetRange z) /\
  (fun _ => True) (MeasObjectEUTRA__widebandRSRQ_Meas z) /\
  True) /\ 
(  opt_cond MeasObjectEUTRA__ext0__cond (MeasObjectEUTRA__ext0 z) /\
  True).


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
Definition MeasObjectEUTRA__cellsToAddModListEUTRAN__Format : T_Format MeasObjectEUTRA__cellsToAddModListEUTRAN__Type MeasObjectEUTRA__cellsToAddModListEUTRAN__cond := seq_of_format EUTRA_Cell__Format 1 maxCellMeasEUTRA MeasObjectEUTRA__cellsToAddModListEUTRAN__helper1 MeasObjectEUTRA__cellsToAddModListEUTRAN__helper2.

Opaque MeasObjectEUTRA__cellsToAddModListEUTRAN__cond MeasObjectEUTRA__cellsToAddModListEUTRAN__Format.

Definition MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__Format : T_Format MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__Type MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__cond := seq_of_format EUTRA_ExcludedCell__Format 1 maxCellMeasEUTRA MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__helper1 MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__helper2.

Opaque MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__cond MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__Format.


Definition MeasObjectEUTRA__ext0O__Format_Type := Eval cbn in seq_format_prod MeasObjectEUTRA__ext0O__list.
Definition MeasObjectEUTRA__ext0O__Format_list : MeasObjectEUTRA__ext0O__Format_Type :=
  (MeasGapId_r17__Format, unit_format).
Definition MeasObjectEUTRA__ext0O__list__Format := (*Eval compute in *) seq_format MeasObjectEUTRA__ext0O__list MeasObjectEUTRA__ext0O__Format_list.
Definition MeasObjectEUTRA__ext0O__F1 z :=
  (MeasObjectEUTRA__ext0O__associatedMeasGap_r17 z, tt).
Definition MeasObjectEUTRA__ext0O__F2 (y : seq_type MeasObjectEUTRA__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__MeasObjectEUTRA__ext0O__Type i0
  end.
Lemma MeasObjectEUTRA__ext0O__F1F2_cond (z : MeasObjectEUTRA__ext0O__Type)
  : MeasObjectEUTRA__ext0O__cond z ->
  (seq_cond MeasObjectEUTRA__ext0O__list (MeasObjectEUTRA__ext0O__F1 z)).
intro H. unfold MeasObjectEUTRA__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasObjectEUTRA__ext0O__F1F2_cond2 (z : MeasObjectEUTRA__ext0O__Type)
 : MeasObjectEUTRA__ext0O__F2 (MeasObjectEUTRA__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasObjectEUTRA__ext0O__F2F1_cond (y : seq_type MeasObjectEUTRA__ext0O__list)
  : seq_cond MeasObjectEUTRA__ext0O__list y ->
 (MeasObjectEUTRA__ext0O__cond (MeasObjectEUTRA__ext0O__F2 y)) /\  MeasObjectEUTRA__ext0O__F1 (MeasObjectEUTRA__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasObjectEUTRA__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasObjectEUTRA__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasObjectEUTRA__ext0O__Format : T_Format MeasObjectEUTRA__ext0O__Type MeasObjectEUTRA__ext0O__cond :=
        proj2_format  MeasObjectEUTRA__ext0O__cond MeasObjectEUTRA__ext0O__list__Format
    MeasObjectEUTRA__ext0O__F1 MeasObjectEUTRA__ext0O__F2 MeasObjectEUTRA__ext0O__F1F2_cond  MeasObjectEUTRA__ext0O__F1F2_cond2 MeasObjectEUTRA__ext0O__F2F1_cond.
Opaque MeasObjectEUTRA__ext0O__cond MeasObjectEUTRA__ext0O__Format.

Definition MeasObjectEUTRA__ext0__check_all_none (b : MeasObjectEUTRA__ext0O__Type) : bool :=
match b with 
  | make__MeasObjectEUTRA__ext0O__Type None  => false 
  | _ => true 
 end.
Definition MeasObjectEUTRA__ext0__Format : T_Format MeasObjectEUTRA__ext0__Type MeasObjectEUTRA__ext0__cond :=
  restrict_add_format MeasObjectEUTRA__ext0__check_all_none MeasObjectEUTRA__ext0O__Format.

Opaque MeasObjectEUTRA__ext0__cond MeasObjectEUTRA__ext0__Format.


Definition MeasObjectEUTRA__root_Format_Type := Eval cbn in seq_format_prod MeasObjectEUTRA__root_list.
Definition MeasObjectEUTRA__root_Format_list : MeasObjectEUTRA__root_Format_Type :=
  (ARFCN_ValueEUTRA__Format, (EUTRA_AllowedMeasBandwidth__Format, (EUTRA_CellIndexList__Format, (MeasObjectEUTRA__cellsToAddModListEUTRAN__Format, (EUTRA_CellIndexList__Format, (MeasObjectEUTRA__excludedCellsToAddModListEUTRAN__Format, (EUTRA_PresenceAntennaPort1__Format, (EUTRA_Q_OffsetRange__Format, (bool__Format, unit_format))))))))).

Definition MeasObjectEUTRA__ext_Format_Type := Eval cbn in get_formats MeasObjectEUTRA__ext_list.
Definition MeasObjectEUTRA__ext_Format_list : MeasObjectEUTRA__ext_Format_Type :=
  (MeasObjectEUTRA__ext0__Format, unit__Format).

Definition MeasObjectEUTRA__list_type : Set := (seq_type MeasObjectEUTRA__root_list) * (seq_ext_type MeasObjectEUTRA__ext_list).
Definition MeasObjectEUTRA__list_cond (z : MeasObjectEUTRA__list_type) : Prop :=
        (seq_cond MeasObjectEUTRA__root_list (fst z)) /\ (seq_ext_cond MeasObjectEUTRA__ext_list (snd z)).
Definition MeasObjectEUTRA__list_format : T_Format MeasObjectEUTRA__list_type MeasObjectEUTRA__list_cond :=
 (* Eval compute in *) seq_ext_format MeasObjectEUTRA__root_list MeasObjectEUTRA__root_Format_list MeasObjectEUTRA__ext_list MeasObjectEUTRA__ext_Format_list.

Opaque MeasObjectEUTRA__list_format.
Definition MeasObjectEUTRA__F1 (z : MeasObjectEUTRA__Type) : MeasObjectEUTRA__list_type :=
  (((MeasObjectEUTRA__carrierFreq z, (MeasObjectEUTRA__allowedMeasBandwidth z, (MeasObjectEUTRA__cellsToRemoveListEUTRAN z, (MeasObjectEUTRA__cellsToAddModListEUTRAN z, (MeasObjectEUTRA__excludedCellsToRemoveListEUTRAN z, (MeasObjectEUTRA__excludedCellsToAddModListEUTRAN z, (MeasObjectEUTRA__eutra_PresenceAntennaPort1 z, (MeasObjectEUTRA__eutra_Q_OffsetRange z, (MeasObjectEUTRA__widebandRSRQ_Meas z, tt)))))))))), (
(MeasObjectEUTRA__ext0 z, tt))).
Definition MeasObjectEUTRA__F2 (y : MeasObjectEUTRA__list_type) : MeasObjectEUTRA__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), (i0, _))=>
    make__MeasObjectEUTRA__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 i0
  end.
Definition MeasObjectEUTRA__helper1 : (forall a : MeasObjectEUTRA__Type, MeasObjectEUTRA__cond a -> MeasObjectEUTRA__list_cond (MeasObjectEUTRA__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasObjectEUTRA__helper2 : (forall a : MeasObjectEUTRA__Type, MeasObjectEUTRA__F2 (MeasObjectEUTRA__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasObjectEUTRA__helper3 : (forall b : MeasObjectEUTRA__list_type, MeasObjectEUTRA__list_cond b -> MeasObjectEUTRA__cond (MeasObjectEUTRA__F2 b) /\ MeasObjectEUTRA__F1 (MeasObjectEUTRA__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasObjectEUTRA__cond, MeasObjectEUTRA__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasObjectEUTRA__Format : T_Format MeasObjectEUTRA__Type MeasObjectEUTRA__cond :=
 proj2_format MeasObjectEUTRA__cond MeasObjectEUTRA__list_format  MeasObjectEUTRA__F1 MeasObjectEUTRA__F2 MeasObjectEUTRA__helper1 MeasObjectEUTRA__helper2 MeasObjectEUTRA__helper3.

Opaque MeasObjectEUTRA__cond MeasObjectEUTRA__Format.

