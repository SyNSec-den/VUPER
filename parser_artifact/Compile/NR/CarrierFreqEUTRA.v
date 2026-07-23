Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Require Import NR.EUTRA_MultiBandInfoList.

Opaque EUTRA_MultiBandInfoList__cond EUTRA_MultiBandInfoList__Format.

Require Import NR.EUTRA_FreqNeighCellList.

Opaque EUTRA_FreqNeighCellList__cond EUTRA_FreqNeighCellList__Format.

Require Import NR.EUTRA_FreqExcludedCellList.

Opaque EUTRA_FreqExcludedCellList__cond EUTRA_FreqExcludedCellList__Format.

Require Import NR.EUTRA_AllowedMeasBandwidth.

Opaque EUTRA_AllowedMeasBandwidth__cond EUTRA_AllowedMeasBandwidth__Format.

Require Import NR.EUTRA_PresenceAntennaPort1.

Opaque EUTRA_PresenceAntennaPort1__cond EUTRA_PresenceAntennaPort1__Format.

Require Import NR.CellReselectionPriority.

Opaque CellReselectionPriority__cond CellReselectionPriority__Format.

Require Import NR.CellReselectionSubPriority.

Opaque CellReselectionSubPriority__cond CellReselectionSubPriority__Format.

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Lemma CarrierFreqEUTRA__q_RxLevMin__helper1 : (-70 <= -22)%Z.  lia. Qed.
Lemma CarrierFreqEUTRA__q_RxLevMin__helper2 : to_bit_sz (Z.to_nat (-22 - -70)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-22 - -70))%Z). { apply Zorder.Zle_minus_le_0. apply CarrierFreqEUTRA__q_RxLevMin__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CarrierFreqEUTRA__q_RxLevMin__Type := Z.
Definition CarrierFreqEUTRA__q_RxLevMin__cond := (fun z => (-70 <= z <= -22)%Z).
Lemma CarrierFreqEUTRA__q_QualMin__helper1 : (-34 <= -3)%Z.  lia. Qed.
Lemma CarrierFreqEUTRA__q_QualMin__helper2 : to_bit_sz (Z.to_nat (-3 - -34)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-3 - -34))%Z). { apply Zorder.Zle_minus_le_0. apply CarrierFreqEUTRA__q_QualMin__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CarrierFreqEUTRA__q_QualMin__Type := Z.
Definition CarrierFreqEUTRA__q_QualMin__cond := (fun z => (-34 <= z <= -3)%Z).
Lemma CarrierFreqEUTRA__p_MaxEUTRA__helper1 : (-30 <= 33)%Z.  lia. Qed.
Lemma CarrierFreqEUTRA__p_MaxEUTRA__helper2 : to_bit_sz (Z.to_nat (33 - -30)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (33 - -30))%Z). { apply Zorder.Zle_minus_le_0. apply CarrierFreqEUTRA__p_MaxEUTRA__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CarrierFreqEUTRA__p_MaxEUTRA__Type := Z.
Definition CarrierFreqEUTRA__p_MaxEUTRA__cond := (fun z => (-30 <= z <= 33)%Z).
Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Record CarrierFreqEUTRA__threshX_Q__Type : Set :=
  make__CarrierFreqEUTRA__threshX_Q__Type {
    CarrierFreqEUTRA__threshX_Q__threshX_HighQ : ReselectionThresholdQ__Type ;
    CarrierFreqEUTRA__threshX_Q__threshX_LowQ : ReselectionThresholdQ__Type ;
}.
Definition CarrierFreqEUTRA__threshX_Q__list := (
 Nor ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 Nor ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 nil).
Definition CarrierFreqEUTRA__threshX_Q__cond z := 
  ReselectionThresholdQ__cond (CarrierFreqEUTRA__threshX_Q__threshX_HighQ z) /\
  ReselectionThresholdQ__cond (CarrierFreqEUTRA__threshX_Q__threshX_LowQ z) /\
  True.

Record CarrierFreqEUTRA__Type : Set :=
  make__CarrierFreqEUTRA__Type {
    CarrierFreqEUTRA__carrierFreq : ARFCN_ValueEUTRA__Type ;
    CarrierFreqEUTRA__eutra_multiBandInfoList : option EUTRA_MultiBandInfoList__Type ;
    CarrierFreqEUTRA__eutra_FreqNeighCellList : option EUTRA_FreqNeighCellList__Type ;
    CarrierFreqEUTRA__eutra_ExcludedCellList : option EUTRA_FreqExcludedCellList__Type ;
    CarrierFreqEUTRA__allowedMeasBandwidth : EUTRA_AllowedMeasBandwidth__Type ;
    CarrierFreqEUTRA__presenceAntennaPort1 : EUTRA_PresenceAntennaPort1__Type ;
    CarrierFreqEUTRA__cellReselectionPriority : option CellReselectionPriority__Type ;
    CarrierFreqEUTRA__cellReselectionSubPriority : option CellReselectionSubPriority__Type ;
    CarrierFreqEUTRA__threshX_High : ReselectionThreshold__Type ;
    CarrierFreqEUTRA__threshX_Low : ReselectionThreshold__Type ;
    CarrierFreqEUTRA__q_RxLevMin : Z ;
    CarrierFreqEUTRA__q_QualMin : Z ;
    CarrierFreqEUTRA__p_MaxEUTRA : Z ;
    CarrierFreqEUTRA__threshX_Q : option CarrierFreqEUTRA__threshX_Q__Type ;
}.
Definition CarrierFreqEUTRA__list := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Opt EUTRA_MultiBandInfoList__Type EUTRA_MultiBandInfoList__cond ::
 Opt EUTRA_FreqNeighCellList__Type EUTRA_FreqNeighCellList__cond ::
 Opt EUTRA_FreqExcludedCellList__Type EUTRA_FreqExcludedCellList__cond ::
 Nor EUTRA_AllowedMeasBandwidth__Type EUTRA_AllowedMeasBandwidth__cond ::
 Nor EUTRA_PresenceAntennaPort1__Type EUTRA_PresenceAntennaPort1__cond ::
 Opt CellReselectionPriority__Type CellReselectionPriority__cond ::
 Opt CellReselectionSubPriority__Type CellReselectionSubPriority__cond ::
 Nor ReselectionThreshold__Type ReselectionThreshold__cond ::
 Nor ReselectionThreshold__Type ReselectionThreshold__cond ::
 Nor Z CarrierFreqEUTRA__q_RxLevMin__cond ::
 Nor Z CarrierFreqEUTRA__q_QualMin__cond ::
 Nor Z CarrierFreqEUTRA__p_MaxEUTRA__cond ::
 Opt CarrierFreqEUTRA__threshX_Q__Type CarrierFreqEUTRA__threshX_Q__cond ::
 nil).
Definition CarrierFreqEUTRA__cond z := 
  ARFCN_ValueEUTRA__cond (CarrierFreqEUTRA__carrierFreq z) /\
  opt_cond EUTRA_MultiBandInfoList__cond (CarrierFreqEUTRA__eutra_multiBandInfoList z) /\
  opt_cond EUTRA_FreqNeighCellList__cond (CarrierFreqEUTRA__eutra_FreqNeighCellList z) /\
  opt_cond EUTRA_FreqExcludedCellList__cond (CarrierFreqEUTRA__eutra_ExcludedCellList z) /\
  EUTRA_AllowedMeasBandwidth__cond (CarrierFreqEUTRA__allowedMeasBandwidth z) /\
  EUTRA_PresenceAntennaPort1__cond (CarrierFreqEUTRA__presenceAntennaPort1 z) /\
  opt_cond CellReselectionPriority__cond (CarrierFreqEUTRA__cellReselectionPriority z) /\
  opt_cond CellReselectionSubPriority__cond (CarrierFreqEUTRA__cellReselectionSubPriority z) /\
  ReselectionThreshold__cond (CarrierFreqEUTRA__threshX_High z) /\
  ReselectionThreshold__cond (CarrierFreqEUTRA__threshX_Low z) /\
  CarrierFreqEUTRA__q_RxLevMin__cond (CarrierFreqEUTRA__q_RxLevMin z) /\
  CarrierFreqEUTRA__q_QualMin__cond (CarrierFreqEUTRA__q_QualMin z) /\
  CarrierFreqEUTRA__p_MaxEUTRA__cond (CarrierFreqEUTRA__p_MaxEUTRA z) /\
  opt_cond CarrierFreqEUTRA__threshX_Q__cond (CarrierFreqEUTRA__threshX_Q z) /\
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
Definition CarrierFreqEUTRA__q_RxLevMin__Format : T_Format Z CarrierFreqEUTRA__q_RxLevMin__cond :=
 ranged_int_format (-70) (-22) CarrierFreqEUTRA__q_RxLevMin__helper1 CarrierFreqEUTRA__q_RxLevMin__helper2.

Opaque CarrierFreqEUTRA__q_RxLevMin__cond CarrierFreqEUTRA__q_RxLevMin__Format.

Definition CarrierFreqEUTRA__q_QualMin__Format : T_Format Z CarrierFreqEUTRA__q_QualMin__cond :=
 ranged_int_format (-34) (-3) CarrierFreqEUTRA__q_QualMin__helper1 CarrierFreqEUTRA__q_QualMin__helper2.

Opaque CarrierFreqEUTRA__q_QualMin__cond CarrierFreqEUTRA__q_QualMin__Format.

Definition CarrierFreqEUTRA__p_MaxEUTRA__Format : T_Format Z CarrierFreqEUTRA__p_MaxEUTRA__cond :=
 ranged_int_format (-30) (33) CarrierFreqEUTRA__p_MaxEUTRA__helper1 CarrierFreqEUTRA__p_MaxEUTRA__helper2.

Opaque CarrierFreqEUTRA__p_MaxEUTRA__cond CarrierFreqEUTRA__p_MaxEUTRA__Format.


Definition CarrierFreqEUTRA__threshX_Q__Format_Type := Eval cbn in seq_format_prod CarrierFreqEUTRA__threshX_Q__list.
Definition CarrierFreqEUTRA__threshX_Q__Format_list : CarrierFreqEUTRA__threshX_Q__Format_Type :=
  (ReselectionThresholdQ__Format, (ReselectionThresholdQ__Format, unit_format)).
Definition CarrierFreqEUTRA__threshX_Q__list__Format := (*Eval compute in *) seq_format CarrierFreqEUTRA__threshX_Q__list CarrierFreqEUTRA__threshX_Q__Format_list.
Definition CarrierFreqEUTRA__threshX_Q__F1 z :=
  (CarrierFreqEUTRA__threshX_Q__threshX_HighQ z, (CarrierFreqEUTRA__threshX_Q__threshX_LowQ z, tt)).
Definition CarrierFreqEUTRA__threshX_Q__F2 (y : seq_type CarrierFreqEUTRA__threshX_Q__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CarrierFreqEUTRA__threshX_Q__Type i0 i1
  end.
Lemma CarrierFreqEUTRA__threshX_Q__F1F2_cond (z : CarrierFreqEUTRA__threshX_Q__Type)
  : CarrierFreqEUTRA__threshX_Q__cond z ->
  (seq_cond CarrierFreqEUTRA__threshX_Q__list (CarrierFreqEUTRA__threshX_Q__F1 z)).
intro H. unfold CarrierFreqEUTRA__threshX_Q__cond in H. simpl. auto. Qed.
Lemma CarrierFreqEUTRA__threshX_Q__F1F2_cond2 (z : CarrierFreqEUTRA__threshX_Q__Type)
 : CarrierFreqEUTRA__threshX_Q__F2 (CarrierFreqEUTRA__threshX_Q__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CarrierFreqEUTRA__threshX_Q__F2F1_cond (y : seq_type CarrierFreqEUTRA__threshX_Q__list)
  : seq_cond CarrierFreqEUTRA__threshX_Q__list y ->
 (CarrierFreqEUTRA__threshX_Q__cond (CarrierFreqEUTRA__threshX_Q__F2 y)) /\  CarrierFreqEUTRA__threshX_Q__F1 (CarrierFreqEUTRA__threshX_Q__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CarrierFreqEUTRA__threshX_Q__cond. simpl in *. auto.
 - simpl. unfold CarrierFreqEUTRA__threshX_Q__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CarrierFreqEUTRA__threshX_Q__Format : T_Format CarrierFreqEUTRA__threshX_Q__Type CarrierFreqEUTRA__threshX_Q__cond :=
        proj2_format  CarrierFreqEUTRA__threshX_Q__cond CarrierFreqEUTRA__threshX_Q__list__Format
    CarrierFreqEUTRA__threshX_Q__F1 CarrierFreqEUTRA__threshX_Q__F2 CarrierFreqEUTRA__threshX_Q__F1F2_cond  CarrierFreqEUTRA__threshX_Q__F1F2_cond2 CarrierFreqEUTRA__threshX_Q__F2F1_cond.
Opaque CarrierFreqEUTRA__threshX_Q__cond CarrierFreqEUTRA__threshX_Q__Format.


Definition CarrierFreqEUTRA__Format_Type := Eval cbn in seq_format_prod CarrierFreqEUTRA__list.
Definition CarrierFreqEUTRA__Format_list : CarrierFreqEUTRA__Format_Type :=
  (ARFCN_ValueEUTRA__Format, (EUTRA_MultiBandInfoList__Format, (EUTRA_FreqNeighCellList__Format, (EUTRA_FreqExcludedCellList__Format, (EUTRA_AllowedMeasBandwidth__Format, (EUTRA_PresenceAntennaPort1__Format, (CellReselectionPriority__Format, (CellReselectionSubPriority__Format, (ReselectionThreshold__Format, (ReselectionThreshold__Format, (CarrierFreqEUTRA__q_RxLevMin__Format, (CarrierFreqEUTRA__q_QualMin__Format, (CarrierFreqEUTRA__p_MaxEUTRA__Format, (CarrierFreqEUTRA__threshX_Q__Format, unit_format)))))))))))))).
Definition CarrierFreqEUTRA__list__Format := (*Eval compute in *) seq_format CarrierFreqEUTRA__list CarrierFreqEUTRA__Format_list.
Definition CarrierFreqEUTRA__F1 z :=
  (CarrierFreqEUTRA__carrierFreq z, (CarrierFreqEUTRA__eutra_multiBandInfoList z, (CarrierFreqEUTRA__eutra_FreqNeighCellList z, (CarrierFreqEUTRA__eutra_ExcludedCellList z, (CarrierFreqEUTRA__allowedMeasBandwidth z, (CarrierFreqEUTRA__presenceAntennaPort1 z, (CarrierFreqEUTRA__cellReselectionPriority z, (CarrierFreqEUTRA__cellReselectionSubPriority z, (CarrierFreqEUTRA__threshX_High z, (CarrierFreqEUTRA__threshX_Low z, (CarrierFreqEUTRA__q_RxLevMin z, (CarrierFreqEUTRA__q_QualMin z, (CarrierFreqEUTRA__p_MaxEUTRA z, (CarrierFreqEUTRA__threshX_Q z, tt)))))))))))))).
Definition CarrierFreqEUTRA__F2 (y : seq_type CarrierFreqEUTRA__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, _))))))))))))))=>
    make__CarrierFreqEUTRA__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  end.
Lemma CarrierFreqEUTRA__F1F2_cond (z : CarrierFreqEUTRA__Type)
  : CarrierFreqEUTRA__cond z ->
  (seq_cond CarrierFreqEUTRA__list (CarrierFreqEUTRA__F1 z)).
intro H. unfold CarrierFreqEUTRA__cond in H. simpl. auto. Qed.
Lemma CarrierFreqEUTRA__F1F2_cond2 (z : CarrierFreqEUTRA__Type)
 : CarrierFreqEUTRA__F2 (CarrierFreqEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CarrierFreqEUTRA__F2F1_cond (y : seq_type CarrierFreqEUTRA__list)
  : seq_cond CarrierFreqEUTRA__list y ->
 (CarrierFreqEUTRA__cond (CarrierFreqEUTRA__F2 y)) /\  CarrierFreqEUTRA__F1 (CarrierFreqEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CarrierFreqEUTRA__cond. simpl in *. auto.
 - simpl. unfold CarrierFreqEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CarrierFreqEUTRA__Format : T_Format CarrierFreqEUTRA__Type CarrierFreqEUTRA__cond :=
        proj2_format  CarrierFreqEUTRA__cond CarrierFreqEUTRA__list__Format
    CarrierFreqEUTRA__F1 CarrierFreqEUTRA__F2 CarrierFreqEUTRA__F1F2_cond  CarrierFreqEUTRA__F1F2_cond2 CarrierFreqEUTRA__F2F1_cond.
Opaque CarrierFreqEUTRA__cond CarrierFreqEUTRA__Format.

