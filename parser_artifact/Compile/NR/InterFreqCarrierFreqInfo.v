Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.MultiFrequencyBandListNR_SIB.

Opaque MultiFrequencyBandListNR_SIB__cond MultiFrequencyBandListNR_SIB__Format.

Require Import NR.MultiFrequencyBandListNR_SIB.

Opaque MultiFrequencyBandListNR_SIB__cond MultiFrequencyBandListNR_SIB__Format.

Lemma InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__helper1 : (2 <= maxNrofSS_BlocksToAverage)%Z. unfold maxNrofSS_BlocksToAverage.
 lia. Qed.
Lemma InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__helper2 : to_bit_sz (Z.to_nat (maxNrofSS_BlocksToAverage - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSS_BlocksToAverage - 2))%Z). { apply Zorder.Zle_minus_le_0. apply InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__Type := Z.
Definition InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__cond := (fun z => (2 <= z <= maxNrofSS_BlocksToAverage)%Z).
Require Import NR.ThresholdNR.

Opaque ThresholdNR__cond ThresholdNR__Format.

Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SSB_ToMeasure.

Opaque SSB_ToMeasure__cond SSB_ToMeasure__Format.

Require Import NR.SS_RSSI_Measurement.

Opaque SS_RSSI_Measurement__cond SS_RSSI_Measurement__Format.

Require Import NR.Q_RxLevMin.

Opaque Q_RxLevMin__cond Q_RxLevMin__Format.

Require Import NR.Q_RxLevMin.

Opaque Q_RxLevMin__cond Q_RxLevMin__Format.

Require Import NR.Q_QualMin.

Opaque Q_QualMin__cond Q_QualMin__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.T_Reselection.

Opaque T_Reselection__cond T_Reselection__Format.

Require Import NR.SpeedStateScaleFactors.

Opaque SpeedStateScaleFactors__cond SpeedStateScaleFactors__Format.

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Record InterFreqCarrierFreqInfo__threshX_Q__Type : Set :=
  make__InterFreqCarrierFreqInfo__threshX_Q__Type {
    InterFreqCarrierFreqInfo__threshX_Q__threshX_HighQ : ReselectionThresholdQ__Type ;
    InterFreqCarrierFreqInfo__threshX_Q__threshX_LowQ : ReselectionThresholdQ__Type ;
}.
Definition InterFreqCarrierFreqInfo__threshX_Q__list := (
 Nor ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 Nor ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 nil).
Definition InterFreqCarrierFreqInfo__threshX_Q__cond z := 
  ReselectionThresholdQ__cond (InterFreqCarrierFreqInfo__threshX_Q__threshX_HighQ z) /\
  ReselectionThresholdQ__cond (InterFreqCarrierFreqInfo__threshX_Q__threshX_LowQ z) /\
  True.

Require Import NR.CellReselectionPriority.

Opaque CellReselectionPriority__cond CellReselectionPriority__Format.

Require Import NR.CellReselectionSubPriority.

Opaque CellReselectionSubPriority__cond CellReselectionSubPriority__Format.

Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma InterFreqCarrierFreqInfo__q_OffsetFreq__dft_helper : Q_OffsetRange__cond Q_OffsetRange__dB0. apply I. Qed.
Definition InterFreqCarrierFreqInfo__q_OffsetFreq__dft_helper2 : forall (x y : Q_OffsetRange__Type), {x = y} + {x <> y}. decide equality. Defined.
Require Import NR.InterFreqNeighCellList.

Opaque InterFreqNeighCellList__cond InterFreqNeighCellList__Format.

Require Import NR.InterFreqExcludedCellList.

Opaque InterFreqExcludedCellList__cond InterFreqExcludedCellList__Format.

Record InterFreqCarrierFreqInfo__Type : Set :=
  make__InterFreqCarrierFreqInfo__Type {
    InterFreqCarrierFreqInfo__dl_CarrierFreq : ARFCN_ValueNR__Type ;
    InterFreqCarrierFreqInfo__frequencyBandList : option MultiFrequencyBandListNR_SIB__Type ;
    InterFreqCarrierFreqInfo__frequencyBandListSUL : option MultiFrequencyBandListNR_SIB__Type ;
    InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage : option Z ;
    InterFreqCarrierFreqInfo__absThreshSS_BlocksConsolidation : option ThresholdNR__Type ;
    InterFreqCarrierFreqInfo__smtc : option SSB_MTC__Type ;
    InterFreqCarrierFreqInfo__ssbSubcarrierSpacing : SubcarrierSpacing__Type ;
    InterFreqCarrierFreqInfo__ssb_ToMeasure : option SSB_ToMeasure__Type ;
    InterFreqCarrierFreqInfo__deriveSSB_IndexFromCell : bool ;
    InterFreqCarrierFreqInfo__ss_RSSI_Measurement : option SS_RSSI_Measurement__Type ;
    InterFreqCarrierFreqInfo__q_RxLevMin : Q_RxLevMin__Type ;
    InterFreqCarrierFreqInfo__q_RxLevMinSUL : option Q_RxLevMin__Type ;
    InterFreqCarrierFreqInfo__q_QualMin : option Q_QualMin__Type ;
    InterFreqCarrierFreqInfo__p_Max : option P_Max__Type ;
    InterFreqCarrierFreqInfo__t_ReselectionNR : T_Reselection__Type ;
    InterFreqCarrierFreqInfo__t_ReselectionNR_SF : option SpeedStateScaleFactors__Type ;
    InterFreqCarrierFreqInfo__threshX_HighP : ReselectionThreshold__Type ;
    InterFreqCarrierFreqInfo__threshX_LowP : ReselectionThreshold__Type ;
    InterFreqCarrierFreqInfo__threshX_Q : option InterFreqCarrierFreqInfo__threshX_Q__Type ;
    InterFreqCarrierFreqInfo__cellReselectionPriority : option CellReselectionPriority__Type ;
    InterFreqCarrierFreqInfo__cellReselectionSubPriority : option CellReselectionSubPriority__Type ;
    InterFreqCarrierFreqInfo__q_OffsetFreq : Q_OffsetRange__Type ;
    InterFreqCarrierFreqInfo__interFreqNeighCellList : option InterFreqNeighCellList__Type ;
    InterFreqCarrierFreqInfo__interFreqExcludedCellList : option InterFreqExcludedCellList__Type ;
}.
Definition InterFreqCarrierFreqInfo__root_list : list seq_elem := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt MultiFrequencyBandListNR_SIB__Type MultiFrequencyBandListNR_SIB__cond ::
 Opt MultiFrequencyBandListNR_SIB__Type MultiFrequencyBandListNR_SIB__cond ::
 Opt Z InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__cond ::
 Opt ThresholdNR__Type ThresholdNR__cond ::
 Opt SSB_MTC__Type SSB_MTC__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt SSB_ToMeasure__Type SSB_ToMeasure__cond ::
 Nor bool (fun _ => True) ::
 Opt SS_RSSI_Measurement__Type SS_RSSI_Measurement__cond ::
 Nor Q_RxLevMin__Type Q_RxLevMin__cond ::
 Opt Q_RxLevMin__Type Q_RxLevMin__cond ::
 Opt Q_QualMin__Type Q_QualMin__cond ::
 Opt P_Max__Type P_Max__cond ::
 Nor T_Reselection__Type T_Reselection__cond ::
 Opt SpeedStateScaleFactors__Type SpeedStateScaleFactors__cond ::
 Nor ReselectionThreshold__Type ReselectionThreshold__cond ::
 Nor ReselectionThreshold__Type ReselectionThreshold__cond ::
 Opt InterFreqCarrierFreqInfo__threshX_Q__Type InterFreqCarrierFreqInfo__threshX_Q__cond ::
 Opt CellReselectionPriority__Type CellReselectionPriority__cond ::
 Opt CellReselectionSubPriority__Type CellReselectionSubPriority__cond ::
 Dft Q_OffsetRange__Type Q_OffsetRange__cond Q_OffsetRange__dB0 InterFreqCarrierFreqInfo__q_OffsetFreq__dft_helper InterFreqCarrierFreqInfo__q_OffsetFreq__dft_helper2 ::
 Opt InterFreqNeighCellList__Type InterFreqNeighCellList__cond ::
 Opt InterFreqExcludedCellList__Type InterFreqExcludedCellList__cond ::
 nil).
Definition InterFreqCarrierFreqInfo__ext_list : list typ := (
  nil).
Definition InterFreqCarrierFreqInfo__cond (z : InterFreqCarrierFreqInfo__Type) := 
(  ARFCN_ValueNR__cond (InterFreqCarrierFreqInfo__dl_CarrierFreq z) /\
  opt_cond MultiFrequencyBandListNR_SIB__cond (InterFreqCarrierFreqInfo__frequencyBandList z) /\
  opt_cond MultiFrequencyBandListNR_SIB__cond (InterFreqCarrierFreqInfo__frequencyBandListSUL z) /\
  opt_cond InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__cond (InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage z) /\
  opt_cond ThresholdNR__cond (InterFreqCarrierFreqInfo__absThreshSS_BlocksConsolidation z) /\
  opt_cond SSB_MTC__cond (InterFreqCarrierFreqInfo__smtc z) /\
  SubcarrierSpacing__cond (InterFreqCarrierFreqInfo__ssbSubcarrierSpacing z) /\
  opt_cond SSB_ToMeasure__cond (InterFreqCarrierFreqInfo__ssb_ToMeasure z) /\
  (fun _ => True) (InterFreqCarrierFreqInfo__deriveSSB_IndexFromCell z) /\
  opt_cond SS_RSSI_Measurement__cond (InterFreqCarrierFreqInfo__ss_RSSI_Measurement z) /\
  Q_RxLevMin__cond (InterFreqCarrierFreqInfo__q_RxLevMin z) /\
  opt_cond Q_RxLevMin__cond (InterFreqCarrierFreqInfo__q_RxLevMinSUL z) /\
  opt_cond Q_QualMin__cond (InterFreqCarrierFreqInfo__q_QualMin z) /\
  opt_cond P_Max__cond (InterFreqCarrierFreqInfo__p_Max z) /\
  T_Reselection__cond (InterFreqCarrierFreqInfo__t_ReselectionNR z) /\
  opt_cond SpeedStateScaleFactors__cond (InterFreqCarrierFreqInfo__t_ReselectionNR_SF z) /\
  ReselectionThreshold__cond (InterFreqCarrierFreqInfo__threshX_HighP z) /\
  ReselectionThreshold__cond (InterFreqCarrierFreqInfo__threshX_LowP z) /\
  opt_cond InterFreqCarrierFreqInfo__threshX_Q__cond (InterFreqCarrierFreqInfo__threshX_Q z) /\
  opt_cond CellReselectionPriority__cond (InterFreqCarrierFreqInfo__cellReselectionPriority z) /\
  opt_cond CellReselectionSubPriority__cond (InterFreqCarrierFreqInfo__cellReselectionSubPriority z) /\
  Q_OffsetRange__cond (InterFreqCarrierFreqInfo__q_OffsetFreq z) /\
  opt_cond InterFreqNeighCellList__cond (InterFreqCarrierFreqInfo__interFreqNeighCellList z) /\
  opt_cond InterFreqExcludedCellList__cond (InterFreqCarrierFreqInfo__interFreqExcludedCellList z) /\
  True) /\ 
(  True).


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
Definition InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__Format : T_Format Z InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__cond :=
 ranged_int_format (2) (maxNrofSS_BlocksToAverage) InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__helper1 InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__helper2.

Opaque InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__cond InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__Format.


Definition InterFreqCarrierFreqInfo__threshX_Q__Format_Type := Eval cbn in seq_format_prod InterFreqCarrierFreqInfo__threshX_Q__list.
Definition InterFreqCarrierFreqInfo__threshX_Q__Format_list : InterFreqCarrierFreqInfo__threshX_Q__Format_Type :=
  (ReselectionThresholdQ__Format, (ReselectionThresholdQ__Format, unit_format)).
Definition InterFreqCarrierFreqInfo__threshX_Q__list__Format := (*Eval compute in *) seq_format InterFreqCarrierFreqInfo__threshX_Q__list InterFreqCarrierFreqInfo__threshX_Q__Format_list.
Definition InterFreqCarrierFreqInfo__threshX_Q__F1 z :=
  (InterFreqCarrierFreqInfo__threshX_Q__threshX_HighQ z, (InterFreqCarrierFreqInfo__threshX_Q__threshX_LowQ z, tt)).
Definition InterFreqCarrierFreqInfo__threshX_Q__F2 (y : seq_type InterFreqCarrierFreqInfo__threshX_Q__list) :=
  match y with
  | (i0, (i1, _))=>
    make__InterFreqCarrierFreqInfo__threshX_Q__Type i0 i1
  end.
Lemma InterFreqCarrierFreqInfo__threshX_Q__F1F2_cond (z : InterFreqCarrierFreqInfo__threshX_Q__Type)
  : InterFreqCarrierFreqInfo__threshX_Q__cond z ->
  (seq_cond InterFreqCarrierFreqInfo__threshX_Q__list (InterFreqCarrierFreqInfo__threshX_Q__F1 z)).
intro H. unfold InterFreqCarrierFreqInfo__threshX_Q__cond in H. simpl. auto. Qed.
Lemma InterFreqCarrierFreqInfo__threshX_Q__F1F2_cond2 (z : InterFreqCarrierFreqInfo__threshX_Q__Type)
 : InterFreqCarrierFreqInfo__threshX_Q__F2 (InterFreqCarrierFreqInfo__threshX_Q__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma InterFreqCarrierFreqInfo__threshX_Q__F2F1_cond (y : seq_type InterFreqCarrierFreqInfo__threshX_Q__list)
  : seq_cond InterFreqCarrierFreqInfo__threshX_Q__list y ->
 (InterFreqCarrierFreqInfo__threshX_Q__cond (InterFreqCarrierFreqInfo__threshX_Q__F2 y)) /\  InterFreqCarrierFreqInfo__threshX_Q__F1 (InterFreqCarrierFreqInfo__threshX_Q__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold InterFreqCarrierFreqInfo__threshX_Q__cond. simpl in *. auto.
 - simpl. unfold InterFreqCarrierFreqInfo__threshX_Q__F1. simpl. destruct_all_unit. auto.   Qed.
Definition InterFreqCarrierFreqInfo__threshX_Q__Format : T_Format InterFreqCarrierFreqInfo__threshX_Q__Type InterFreqCarrierFreqInfo__threshX_Q__cond :=
        proj2_format  InterFreqCarrierFreqInfo__threshX_Q__cond InterFreqCarrierFreqInfo__threshX_Q__list__Format
    InterFreqCarrierFreqInfo__threshX_Q__F1 InterFreqCarrierFreqInfo__threshX_Q__F2 InterFreqCarrierFreqInfo__threshX_Q__F1F2_cond  InterFreqCarrierFreqInfo__threshX_Q__F1F2_cond2 InterFreqCarrierFreqInfo__threshX_Q__F2F1_cond.
Opaque InterFreqCarrierFreqInfo__threshX_Q__cond InterFreqCarrierFreqInfo__threshX_Q__Format.


Definition InterFreqCarrierFreqInfo__root_Format_Type := Eval cbn in seq_format_prod InterFreqCarrierFreqInfo__root_list.
Definition InterFreqCarrierFreqInfo__root_Format_list : InterFreqCarrierFreqInfo__root_Format_Type :=
  (ARFCN_ValueNR__Format, (MultiFrequencyBandListNR_SIB__Format, (MultiFrequencyBandListNR_SIB__Format, (InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage__Format, (ThresholdNR__Format, (SSB_MTC__Format, (SubcarrierSpacing__Format, (SSB_ToMeasure__Format, (bool__Format, (SS_RSSI_Measurement__Format, (Q_RxLevMin__Format, (Q_RxLevMin__Format, (Q_QualMin__Format, (P_Max__Format, (T_Reselection__Format, (SpeedStateScaleFactors__Format, (ReselectionThreshold__Format, (ReselectionThreshold__Format, (InterFreqCarrierFreqInfo__threshX_Q__Format, (CellReselectionPriority__Format, (CellReselectionSubPriority__Format, (Q_OffsetRange__Format, (InterFreqNeighCellList__Format, (InterFreqExcludedCellList__Format, unit_format)))))))))))))))))))))))).

Definition InterFreqCarrierFreqInfo__ext_Format_Type := Eval cbn in get_formats InterFreqCarrierFreqInfo__ext_list.
Definition InterFreqCarrierFreqInfo__ext_Format_list : InterFreqCarrierFreqInfo__ext_Format_Type :=
  unit__Format.

Definition InterFreqCarrierFreqInfo__list_type : Set := (seq_type InterFreqCarrierFreqInfo__root_list) * (seq_ext_type InterFreqCarrierFreqInfo__ext_list).
Definition InterFreqCarrierFreqInfo__list_cond (z : InterFreqCarrierFreqInfo__list_type) : Prop :=
        (seq_cond InterFreqCarrierFreqInfo__root_list (fst z)) /\ (seq_ext_cond InterFreqCarrierFreqInfo__ext_list (snd z)).
Definition InterFreqCarrierFreqInfo__list_format : T_Format InterFreqCarrierFreqInfo__list_type InterFreqCarrierFreqInfo__list_cond :=
 (* Eval compute in *) seq_ext_format InterFreqCarrierFreqInfo__root_list InterFreqCarrierFreqInfo__root_Format_list InterFreqCarrierFreqInfo__ext_list InterFreqCarrierFreqInfo__ext_Format_list.

Opaque InterFreqCarrierFreqInfo__list_format.
Definition InterFreqCarrierFreqInfo__F1 (z : InterFreqCarrierFreqInfo__Type) : InterFreqCarrierFreqInfo__list_type :=
  (((InterFreqCarrierFreqInfo__dl_CarrierFreq z, (InterFreqCarrierFreqInfo__frequencyBandList z, (InterFreqCarrierFreqInfo__frequencyBandListSUL z, (InterFreqCarrierFreqInfo__nrofSS_BlocksToAverage z, (InterFreqCarrierFreqInfo__absThreshSS_BlocksConsolidation z, (InterFreqCarrierFreqInfo__smtc z, (InterFreqCarrierFreqInfo__ssbSubcarrierSpacing z, (InterFreqCarrierFreqInfo__ssb_ToMeasure z, (InterFreqCarrierFreqInfo__deriveSSB_IndexFromCell z, (InterFreqCarrierFreqInfo__ss_RSSI_Measurement z, (InterFreqCarrierFreqInfo__q_RxLevMin z, (InterFreqCarrierFreqInfo__q_RxLevMinSUL z, (InterFreqCarrierFreqInfo__q_QualMin z, (InterFreqCarrierFreqInfo__p_Max z, (InterFreqCarrierFreqInfo__t_ReselectionNR z, (InterFreqCarrierFreqInfo__t_ReselectionNR_SF z, (InterFreqCarrierFreqInfo__threshX_HighP z, (InterFreqCarrierFreqInfo__threshX_LowP z, (InterFreqCarrierFreqInfo__threshX_Q z, (InterFreqCarrierFreqInfo__cellReselectionPriority z, (InterFreqCarrierFreqInfo__cellReselectionSubPriority z, (InterFreqCarrierFreqInfo__q_OffsetFreq z, (InterFreqCarrierFreqInfo__interFreqNeighCellList z, (InterFreqCarrierFreqInfo__interFreqExcludedCellList z, tt))))))))))))))))))))))))), (
tt)).
Definition InterFreqCarrierFreqInfo__F2 (y : InterFreqCarrierFreqInfo__list_type) : InterFreqCarrierFreqInfo__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, (j18, (j19, (j20, (j21, (j22, (j23, _)))))))))))))))))))))))), _)=>
    make__InterFreqCarrierFreqInfo__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j22 j23
  end.
Definition InterFreqCarrierFreqInfo__helper1 : (forall a : InterFreqCarrierFreqInfo__Type, InterFreqCarrierFreqInfo__cond a -> InterFreqCarrierFreqInfo__list_cond (InterFreqCarrierFreqInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition InterFreqCarrierFreqInfo__helper2 : (forall a : InterFreqCarrierFreqInfo__Type, InterFreqCarrierFreqInfo__F2 (InterFreqCarrierFreqInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition InterFreqCarrierFreqInfo__helper3 : (forall b : InterFreqCarrierFreqInfo__list_type, InterFreqCarrierFreqInfo__list_cond b -> InterFreqCarrierFreqInfo__cond (InterFreqCarrierFreqInfo__F2 b) /\ InterFreqCarrierFreqInfo__F1 (InterFreqCarrierFreqInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold InterFreqCarrierFreqInfo__cond, InterFreqCarrierFreqInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition InterFreqCarrierFreqInfo__Format : T_Format InterFreqCarrierFreqInfo__Type InterFreqCarrierFreqInfo__cond :=
 proj2_format InterFreqCarrierFreqInfo__cond InterFreqCarrierFreqInfo__list_format  InterFreqCarrierFreqInfo__F1 InterFreqCarrierFreqInfo__F2 InterFreqCarrierFreqInfo__helper1 InterFreqCarrierFreqInfo__helper2 InterFreqCarrierFreqInfo__helper3.

Opaque InterFreqCarrierFreqInfo__cond InterFreqCarrierFreqInfo__Format.

