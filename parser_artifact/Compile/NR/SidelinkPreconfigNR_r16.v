Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_Sidelink_Preconf.
Require Import NR.SL_FreqConfigCommon_r16.

Opaque SL_FreqConfigCommon_r16__cond SL_FreqConfigCommon_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__Type := list SL_FreqConfigCommon_r16__Type.

Lemma SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__helper1 : (0 <= 1 <= maxNrofFreqSL_r16)%Z. unfold maxNrofFreqSL_r16.
 lia. Qed.
Lemma SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofFreqSL_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofFreqSL_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__cond (z : SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofFreqSL_r16)%Z /\ (list_and SL_FreqConfigCommon_r16__cond z) .

Require Import NR.SL_NR_AnchorCarrierFreqList_r16.

Opaque SL_NR_AnchorCarrierFreqList_r16__cond SL_NR_AnchorCarrierFreqList_r16__Format.

Require Import NR.SL_EUTRA_AnchorCarrierFreqList_r16.

Opaque SL_EUTRA_AnchorCarrierFreqList_r16__cond SL_EUTRA_AnchorCarrierFreqList_r16__Format.

Require Import NR.SL_RadioBearerConfig_r16.

Opaque SL_RadioBearerConfig_r16__cond SL_RadioBearerConfig_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__Type := list SL_RadioBearerConfig_r16__Type.

Lemma SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__helper1 : (0 <= 1 <= maxNrofSLRB_r16)%Z. unfold maxNrofSLRB_r16.
 lia. Qed.
Lemma SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSLRB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSLRB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__cond (z : SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSLRB_r16)%Z /\ (list_and SL_RadioBearerConfig_r16__cond z) .

Require Import NR.SL_RLC_BearerConfig_r16.

Opaque SL_RLC_BearerConfig_r16__cond SL_RLC_BearerConfig_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__Type := list SL_RLC_BearerConfig_r16__Type.

Lemma SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__helper1 : (0 <= 1 <= maxSL_LCID_r16)%Z. unfold maxSL_LCID_r16.
 lia. Qed.
Lemma SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__helper2 : to_bit_sz (Z.to_nat (maxSL_LCID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSL_LCID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__cond (z : SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSL_LCID_r16)%Z /\ (list_and SL_RLC_BearerConfig_r16__cond z) .

Require Import NR.SL_MeasConfigCommon_r16.

Opaque SL_MeasConfigCommon_r16__cond SL_MeasConfigCommon_r16__Format.

Lemma SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__helper1 : (1 <= 1000)%Z.  lia. Qed.
Lemma SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__helper2 : to_bit_sz (Z.to_nat (1000 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1000 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__Type := Z.
Definition SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__cond := (fun z => (1 <= z <= 1000)%Z).
Inductive SidelinkPreconfigNR_r16__t400_r16__Type : Set :=
 | SidelinkPreconfigNR_r16__t400_r16__ms100
 | SidelinkPreconfigNR_r16__t400_r16__ms200
 | SidelinkPreconfigNR_r16__t400_r16__ms300
 | SidelinkPreconfigNR_r16__t400_r16__ms400
 | SidelinkPreconfigNR_r16__t400_r16__ms600
 | SidelinkPreconfigNR_r16__t400_r16__ms1000
 | SidelinkPreconfigNR_r16__t400_r16__ms1500
 | SidelinkPreconfigNR_r16__t400_r16__ms2000
.
Definition SidelinkPreconfigNR_r16__t400_r16__cond := (fun (_ : SidelinkPreconfigNR_r16__t400_r16__Type) => True).
Lemma SidelinkPreconfigNR_r16__t400_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SidelinkPreconfigNR_r16__t400_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SidelinkPreconfigNR_r16__t400_r16__nat__helper.

Definition SidelinkPreconfigNR_r16__t400_r16__F1 t :=
  match t with
  | SidelinkPreconfigNR_r16__t400_r16__ms100 => 0
  | SidelinkPreconfigNR_r16__t400_r16__ms200 => 1
  | SidelinkPreconfigNR_r16__t400_r16__ms300 => 2
  | SidelinkPreconfigNR_r16__t400_r16__ms400 => 3
  | SidelinkPreconfigNR_r16__t400_r16__ms600 => 4
  | SidelinkPreconfigNR_r16__t400_r16__ms1000 => 5
  | SidelinkPreconfigNR_r16__t400_r16__ms1500 => 6
  | SidelinkPreconfigNR_r16__t400_r16__ms2000 => 7
  end.
Definition SidelinkPreconfigNR_r16__t400_r16__F2 n :=
  match n with
  | 0 => SidelinkPreconfigNR_r16__t400_r16__ms100
  | 1 => SidelinkPreconfigNR_r16__t400_r16__ms200
  | 2 => SidelinkPreconfigNR_r16__t400_r16__ms300
  | 3 => SidelinkPreconfigNR_r16__t400_r16__ms400
  | 4 => SidelinkPreconfigNR_r16__t400_r16__ms600
  | 5 => SidelinkPreconfigNR_r16__t400_r16__ms1000
  | 6 => SidelinkPreconfigNR_r16__t400_r16__ms1500
  | 7 => SidelinkPreconfigNR_r16__t400_r16__ms2000
  | _ => SidelinkPreconfigNR_r16__t400_r16__ms100
  end.
Lemma SidelinkPreconfigNR_r16__t400_r16__F1F2 : forall x : SidelinkPreconfigNR_r16__t400_r16__Type, (SidelinkPreconfigNR_r16__t400_r16__F1 x <= 7) /\ SidelinkPreconfigNR_r16__t400_r16__F2 (SidelinkPreconfigNR_r16__t400_r16__F1 x) = x. imp_solve. Qed.
Lemma SidelinkPreconfigNR_r16__t400_r16__F2F1 : forall (y : nat) (H : y <= 7), SidelinkPreconfigNR_r16__t400_r16__F1 (SidelinkPreconfigNR_r16__t400_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Type : Set :=
 | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n1
 | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n2
 | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n3
 | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n4
 | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n6
 | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n8
 | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n16
 | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n32
.
Definition SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__cond := (fun (_ : SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Type) => True).
Lemma SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__nat__helper.

Definition SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 t :=
  match t with
  | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n1 => 0
  | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n2 => 1
  | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n3 => 2
  | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n4 => 3
  | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n6 => 4
  | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n8 => 5
  | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n16 => 6
  | SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n32 => 7
  end.
Definition SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F2 n :=
  match n with
  | 0 => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n1
  | 1 => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n2
  | 2 => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n3
  | 3 => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n4
  | 4 => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n6
  | 5 => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n8
  | 6 => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n16
  | 7 => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n32
  | _ => SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__n1
  end.
Lemma SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F1F2 : forall x : SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Type, (SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 x <= 7) /\ SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F2 (SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 x) = x. imp_solve. Qed.
Lemma SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F2F1 : forall (y : nat) (H : y <= 7), SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 (SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__Type := Z.
Definition SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__cond := (fun z => (1 <= z <= 8)%Z).
Require Import NR.SL_PreconfigGeneral_r16.

Opaque SL_PreconfigGeneral_r16__cond SL_PreconfigGeneral_r16__Format.

Require Import NR.SL_UE_SelectedConfig_r16.

Opaque SL_UE_SelectedConfig_r16__cond SL_UE_SelectedConfig_r16__Format.

Inductive SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Type : Set :=
 | SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__enabled
.
Definition SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__cond := (fun (_ : SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Type) => True).
Lemma SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__nat__helper.

Definition SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F1 t :=
  match t with
  | SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__enabled => 0
  end.
Definition SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F2 n :=
  match n with
  | 0 => SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__enabled
  | _ => SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__enabled
  end.
Lemma SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F1F2 : forall x : SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Type, (SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F1 x <= 0) /\ SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F2 (SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F1 x) = x. imp_solve. Qed.
Lemma SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F2F1 : forall (y : nat) (H : y <= 0), SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F1 (SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_RoHC_Profiles_r16.

Opaque SL_RoHC_Profiles_r16__cond SL_RoHC_Profiles_r16__Format.

Lemma SidelinkPreconfigNR_r16__sl_MaxCID_r16__helper1 : (1 <= 16383)%Z.  lia. Qed.
Lemma SidelinkPreconfigNR_r16__sl_MaxCID_r16__helper2 : to_bit_sz (Z.to_nat (16383 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16383 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SidelinkPreconfigNR_r16__sl_MaxCID_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SidelinkPreconfigNR_r16__sl_MaxCID_r16__Type := Z.
Definition SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond := (fun z => (1 <= z <= 16383)%Z).
Transparent SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond.
Lemma SidelinkPreconfigNR_r16__sl_MaxCID_r16__dft_helper : SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond 15. unfold SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond. lia. Qed.
Opaque SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond.
Require Import NR.SL_DRX_ConfigGC_BC_r17.

Opaque SL_DRX_ConfigGC_BC_r17__cond SL_DRX_ConfigGC_BC_r17__Format.

Require Import NR.SL_TxProfileList_r17.

Opaque SL_TxProfileList_r17__cond SL_TxProfileList_r17__Format.

Require Import NR.SL_RemoteUE_Config_r17.

Opaque SL_RemoteUE_Config_r17__cond SL_RemoteUE_Config_r17__Format.

Record SidelinkPreconfigNR_r16__ext0O__Type : Set :=
  make__SidelinkPreconfigNR_r16__ext0O__Type {
    SidelinkPreconfigNR_r16__ext0O__sl_DRX_PreConfigGC_BC_r17 : option SL_DRX_ConfigGC_BC_r17__Type ;
    SidelinkPreconfigNR_r16__ext0O__sl_TxProfileList_r17 : option SL_TxProfileList_r17__Type ;
    SidelinkPreconfigNR_r16__ext0O__sl_PreconfigDiscConfig_r17 : option SL_RemoteUE_Config_r17__Type ;
}.
Definition SidelinkPreconfigNR_r16__ext0O__list := (
 Opt SL_DRX_ConfigGC_BC_r17__Type SL_DRX_ConfigGC_BC_r17__cond ::
 Opt SL_TxProfileList_r17__Type SL_TxProfileList_r17__cond ::
 Opt SL_RemoteUE_Config_r17__Type SL_RemoteUE_Config_r17__cond ::
 nil).
Definition SidelinkPreconfigNR_r16__ext0O__cond z := 
  opt_cond SL_DRX_ConfigGC_BC_r17__cond (SidelinkPreconfigNR_r16__ext0O__sl_DRX_PreConfigGC_BC_r17 z) /\
  opt_cond SL_TxProfileList_r17__cond (SidelinkPreconfigNR_r16__ext0O__sl_TxProfileList_r17 z) /\
  opt_cond SL_RemoteUE_Config_r17__cond (SidelinkPreconfigNR_r16__ext0O__sl_PreconfigDiscConfig_r17 z) /\
  True.

Definition SidelinkPreconfigNR_r16__ext0__Type := SidelinkPreconfigNR_r16__ext0O__Type.
Definition SidelinkPreconfigNR_r16__ext0__cond := SidelinkPreconfigNR_r16__ext0O__cond.

Record SidelinkPreconfigNR_r16__Type : Set :=
  make__SidelinkPreconfigNR_r16__Type {
    SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16 : option SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__Type ;
    SidelinkPreconfigNR_r16__sl_PreconfigNR_AnchorCarrierFreqList_r16 : option SL_NR_AnchorCarrierFreqList_r16__Type ;
    SidelinkPreconfigNR_r16__sl_PreconfigEUTRA_AnchorCarrierFreqList_r16 : option SL_EUTRA_AnchorCarrierFreqList_r16__Type ;
    SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16 : option SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__Type ;
    SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16 : option SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__Type ;
    SidelinkPreconfigNR_r16__sl_MeasPreConfig_r16 : option SL_MeasConfigCommon_r16__Type ;
    SidelinkPreconfigNR_r16__sl_OffsetDFN_r16 : option Z ;
    SidelinkPreconfigNR_r16__t400_r16 : option SidelinkPreconfigNR_r16__t400_r16__Type ;
    SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16 : option SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Type ;
    SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16 : option Z ;
    SidelinkPreconfigNR_r16__sl_PreconfigGeneral_r16 : option SL_PreconfigGeneral_r16__Type ;
    SidelinkPreconfigNR_r16__sl_UE_SelectedPreConfig_r16 : option SL_UE_SelectedConfig_r16__Type ;
    SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16 : option SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Type ;
    SidelinkPreconfigNR_r16__sl_RoHC_Profiles_r16 : option SL_RoHC_Profiles_r16__Type ;
    SidelinkPreconfigNR_r16__sl_MaxCID_r16 : Z ;
    SidelinkPreconfigNR_r16__ext0 : option SidelinkPreconfigNR_r16__ext0__Type ;
}.
Definition SidelinkPreconfigNR_r16__root_list : list seq_elem := (
 Opt SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__Type SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__cond ::
 Opt SL_NR_AnchorCarrierFreqList_r16__Type SL_NR_AnchorCarrierFreqList_r16__cond ::
 Opt SL_EUTRA_AnchorCarrierFreqList_r16__Type SL_EUTRA_AnchorCarrierFreqList_r16__cond ::
 Opt SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__Type SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__cond ::
 Opt SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__Type SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__cond ::
 Opt SL_MeasConfigCommon_r16__Type SL_MeasConfigCommon_r16__cond ::
 Opt Z SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__cond ::
 Opt SidelinkPreconfigNR_r16__t400_r16__Type SidelinkPreconfigNR_r16__t400_r16__cond ::
 Opt SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Type SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__cond ::
 Opt Z SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__cond ::
 Opt SL_PreconfigGeneral_r16__Type SL_PreconfigGeneral_r16__cond ::
 Opt SL_UE_SelectedConfig_r16__Type SL_UE_SelectedConfig_r16__cond ::
 Opt SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Type SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__cond ::
 Opt SL_RoHC_Profiles_r16__Type SL_RoHC_Profiles_r16__cond ::
 Dft Z SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond 15%Z SidelinkPreconfigNR_r16__sl_MaxCID_r16__dft_helper Z.eq_dec ::
 nil).
Definition SidelinkPreconfigNR_r16__ext_list : list typ := (
  typ_cons SidelinkPreconfigNR_r16__ext0__Type SidelinkPreconfigNR_r16__ext0__cond ::
  nil).
Definition SidelinkPreconfigNR_r16__cond (z : SidelinkPreconfigNR_r16__Type) := 
(  opt_cond SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__cond (SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16 z) /\
  opt_cond SL_NR_AnchorCarrierFreqList_r16__cond (SidelinkPreconfigNR_r16__sl_PreconfigNR_AnchorCarrierFreqList_r16 z) /\
  opt_cond SL_EUTRA_AnchorCarrierFreqList_r16__cond (SidelinkPreconfigNR_r16__sl_PreconfigEUTRA_AnchorCarrierFreqList_r16 z) /\
  opt_cond SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__cond (SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16 z) /\
  opt_cond SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__cond (SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16 z) /\
  opt_cond SL_MeasConfigCommon_r16__cond (SidelinkPreconfigNR_r16__sl_MeasPreConfig_r16 z) /\
  opt_cond SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__cond (SidelinkPreconfigNR_r16__sl_OffsetDFN_r16 z) /\
  opt_cond SidelinkPreconfigNR_r16__t400_r16__cond (SidelinkPreconfigNR_r16__t400_r16 z) /\
  opt_cond SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__cond (SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16 z) /\
  opt_cond SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__cond (SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16 z) /\
  opt_cond SL_PreconfigGeneral_r16__cond (SidelinkPreconfigNR_r16__sl_PreconfigGeneral_r16 z) /\
  opt_cond SL_UE_SelectedConfig_r16__cond (SidelinkPreconfigNR_r16__sl_UE_SelectedPreConfig_r16 z) /\
  opt_cond SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__cond (SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16 z) /\
  opt_cond SL_RoHC_Profiles_r16__cond (SidelinkPreconfigNR_r16__sl_RoHC_Profiles_r16 z) /\
  SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond (SidelinkPreconfigNR_r16__sl_MaxCID_r16 z) /\
  True) /\ 
(  opt_cond SidelinkPreconfigNR_r16__ext0__cond (SidelinkPreconfigNR_r16__ext0 z) /\
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
Definition SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__Format : T_Format SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__Type SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__cond := seq_of_format SL_FreqConfigCommon_r16__Format 1 maxNrofFreqSL_r16 SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__helper1 SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__helper2.

Opaque SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__cond SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__Format : T_Format SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__Type SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__cond := seq_of_format SL_RadioBearerConfig_r16__Format 1 maxNrofSLRB_r16 SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__helper1 SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__helper2.

Opaque SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__cond SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__Format : T_Format SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__Type SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__cond := seq_of_format SL_RLC_BearerConfig_r16__Format 1 maxSL_LCID_r16 SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__helper1 SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__helper2.

Opaque SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__cond SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__Format : T_Format Z SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__cond :=
 ranged_int_format (1) (1000) SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__helper1 SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__helper2.

Opaque SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__cond SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__Format.

Definition SidelinkPreconfigNR_r16__t400_r16__Format : T_Format SidelinkPreconfigNR_r16__t400_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SidelinkPreconfigNR_r16__t400_r16__nat__Format SidelinkPreconfigNR_r16__t400_r16__F1 SidelinkPreconfigNR_r16__t400_r16__F2 SidelinkPreconfigNR_r16__t400_r16__F1F2 SidelinkPreconfigNR_r16__t400_r16__F2F1.

Opaque SidelinkPreconfigNR_r16__t400_r16__cond SidelinkPreconfigNR_r16__t400_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Format : T_Format SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__nat__Format SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F2 SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F1F2 SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__F2F1.

Opaque SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__cond SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__Format : T_Format Z SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__cond :=
 ranged_int_format (1) (8) SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__helper1 SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__helper2.

Opaque SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__cond SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Format : T_Format SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__nat__Format SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F1 SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F2 SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F1F2 SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__F2F1.

Opaque SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__cond SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Format.

Definition SidelinkPreconfigNR_r16__sl_MaxCID_r16__Format : T_Format Z SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond :=
 ranged_int_format (1) (16383) SidelinkPreconfigNR_r16__sl_MaxCID_r16__helper1 SidelinkPreconfigNR_r16__sl_MaxCID_r16__helper2.

Opaque SidelinkPreconfigNR_r16__sl_MaxCID_r16__cond SidelinkPreconfigNR_r16__sl_MaxCID_r16__Format.


Definition SidelinkPreconfigNR_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SidelinkPreconfigNR_r16__ext0O__list.
Definition SidelinkPreconfigNR_r16__ext0O__Format_list : SidelinkPreconfigNR_r16__ext0O__Format_Type :=
  (SL_DRX_ConfigGC_BC_r17__Format, (SL_TxProfileList_r17__Format, (SL_RemoteUE_Config_r17__Format, unit_format))).
Definition SidelinkPreconfigNR_r16__ext0O__list__Format := (*Eval compute in *) seq_format SidelinkPreconfigNR_r16__ext0O__list SidelinkPreconfigNR_r16__ext0O__Format_list.
Definition SidelinkPreconfigNR_r16__ext0O__F1 z :=
  (SidelinkPreconfigNR_r16__ext0O__sl_DRX_PreConfigGC_BC_r17 z, (SidelinkPreconfigNR_r16__ext0O__sl_TxProfileList_r17 z, (SidelinkPreconfigNR_r16__ext0O__sl_PreconfigDiscConfig_r17 z, tt))).
Definition SidelinkPreconfigNR_r16__ext0O__F2 (y : seq_type SidelinkPreconfigNR_r16__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SidelinkPreconfigNR_r16__ext0O__Type i0 i1 i2
  end.
Lemma SidelinkPreconfigNR_r16__ext0O__F1F2_cond (z : SidelinkPreconfigNR_r16__ext0O__Type)
  : SidelinkPreconfigNR_r16__ext0O__cond z ->
  (seq_cond SidelinkPreconfigNR_r16__ext0O__list (SidelinkPreconfigNR_r16__ext0O__F1 z)).
intro H. unfold SidelinkPreconfigNR_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SidelinkPreconfigNR_r16__ext0O__F1F2_cond2 (z : SidelinkPreconfigNR_r16__ext0O__Type)
 : SidelinkPreconfigNR_r16__ext0O__F2 (SidelinkPreconfigNR_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SidelinkPreconfigNR_r16__ext0O__F2F1_cond (y : seq_type SidelinkPreconfigNR_r16__ext0O__list)
  : seq_cond SidelinkPreconfigNR_r16__ext0O__list y ->
 (SidelinkPreconfigNR_r16__ext0O__cond (SidelinkPreconfigNR_r16__ext0O__F2 y)) /\  SidelinkPreconfigNR_r16__ext0O__F1 (SidelinkPreconfigNR_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SidelinkPreconfigNR_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SidelinkPreconfigNR_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SidelinkPreconfigNR_r16__ext0O__Format : T_Format SidelinkPreconfigNR_r16__ext0O__Type SidelinkPreconfigNR_r16__ext0O__cond :=
        proj2_format  SidelinkPreconfigNR_r16__ext0O__cond SidelinkPreconfigNR_r16__ext0O__list__Format
    SidelinkPreconfigNR_r16__ext0O__F1 SidelinkPreconfigNR_r16__ext0O__F2 SidelinkPreconfigNR_r16__ext0O__F1F2_cond  SidelinkPreconfigNR_r16__ext0O__F1F2_cond2 SidelinkPreconfigNR_r16__ext0O__F2F1_cond.
Opaque SidelinkPreconfigNR_r16__ext0O__cond SidelinkPreconfigNR_r16__ext0O__Format.

Definition SidelinkPreconfigNR_r16__ext0__check_all_none (b : SidelinkPreconfigNR_r16__ext0O__Type) : bool :=
match b with 
  | make__SidelinkPreconfigNR_r16__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition SidelinkPreconfigNR_r16__ext0__Format : T_Format SidelinkPreconfigNR_r16__ext0__Type SidelinkPreconfigNR_r16__ext0__cond :=
  restrict_add_format SidelinkPreconfigNR_r16__ext0__check_all_none SidelinkPreconfigNR_r16__ext0O__Format.

Opaque SidelinkPreconfigNR_r16__ext0__cond SidelinkPreconfigNR_r16__ext0__Format.


Definition SidelinkPreconfigNR_r16__root_Format_Type := Eval cbn in seq_format_prod SidelinkPreconfigNR_r16__root_list.
Definition SidelinkPreconfigNR_r16__root_Format_list : SidelinkPreconfigNR_r16__root_Format_Type :=
  (SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16__Format, (SL_NR_AnchorCarrierFreqList_r16__Format, (SL_EUTRA_AnchorCarrierFreqList_r16__Format, (SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16__Format, (SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16__Format, (SL_MeasConfigCommon_r16__Format, (SidelinkPreconfigNR_r16__sl_OffsetDFN_r16__Format, (SidelinkPreconfigNR_r16__t400_r16__Format, (SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16__Format, (SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16__Format, (SL_PreconfigGeneral_r16__Format, (SL_UE_SelectedConfig_r16__Format, (SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16__Format, (SL_RoHC_Profiles_r16__Format, (SidelinkPreconfigNR_r16__sl_MaxCID_r16__Format, unit_format))))))))))))))).

Definition SidelinkPreconfigNR_r16__ext_Format_Type := Eval cbn in get_formats SidelinkPreconfigNR_r16__ext_list.
Definition SidelinkPreconfigNR_r16__ext_Format_list : SidelinkPreconfigNR_r16__ext_Format_Type :=
  (SidelinkPreconfigNR_r16__ext0__Format, unit__Format).

Definition SidelinkPreconfigNR_r16__list_type : Set := (seq_type SidelinkPreconfigNR_r16__root_list) * (seq_ext_type SidelinkPreconfigNR_r16__ext_list).
Definition SidelinkPreconfigNR_r16__list_cond (z : SidelinkPreconfigNR_r16__list_type) : Prop :=
        (seq_cond SidelinkPreconfigNR_r16__root_list (fst z)) /\ (seq_ext_cond SidelinkPreconfigNR_r16__ext_list (snd z)).
Definition SidelinkPreconfigNR_r16__list_format : T_Format SidelinkPreconfigNR_r16__list_type SidelinkPreconfigNR_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SidelinkPreconfigNR_r16__root_list SidelinkPreconfigNR_r16__root_Format_list SidelinkPreconfigNR_r16__ext_list SidelinkPreconfigNR_r16__ext_Format_list.

Opaque SidelinkPreconfigNR_r16__list_format.
Definition SidelinkPreconfigNR_r16__F1 (z : SidelinkPreconfigNR_r16__Type) : SidelinkPreconfigNR_r16__list_type :=
  (((SidelinkPreconfigNR_r16__sl_PreconfigFreqInfoList_r16 z, (SidelinkPreconfigNR_r16__sl_PreconfigNR_AnchorCarrierFreqList_r16 z, (SidelinkPreconfigNR_r16__sl_PreconfigEUTRA_AnchorCarrierFreqList_r16 z, (SidelinkPreconfigNR_r16__sl_RadioBearerPreConfigList_r16 z, (SidelinkPreconfigNR_r16__sl_RLC_BearerPreConfigList_r16 z, (SidelinkPreconfigNR_r16__sl_MeasPreConfig_r16 z, (SidelinkPreconfigNR_r16__sl_OffsetDFN_r16 z, (SidelinkPreconfigNR_r16__t400_r16 z, (SidelinkPreconfigNR_r16__sl_MaxNumConsecutiveDTX_r16 z, (SidelinkPreconfigNR_r16__sl_SSB_PriorityNR_r16 z, (SidelinkPreconfigNR_r16__sl_PreconfigGeneral_r16 z, (SidelinkPreconfigNR_r16__sl_UE_SelectedPreConfig_r16 z, (SidelinkPreconfigNR_r16__sl_CSI_Acquisition_r16 z, (SidelinkPreconfigNR_r16__sl_RoHC_Profiles_r16 z, (SidelinkPreconfigNR_r16__sl_MaxCID_r16 z, tt)))))))))))))))), (
(SidelinkPreconfigNR_r16__ext0 z, tt))).
Definition SidelinkPreconfigNR_r16__F2 (y : SidelinkPreconfigNR_r16__list_type) : SidelinkPreconfigNR_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, _))))))))))))))), (i0, _))=>
    make__SidelinkPreconfigNR_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 i0
  end.
Definition SidelinkPreconfigNR_r16__helper1 : (forall a : SidelinkPreconfigNR_r16__Type, SidelinkPreconfigNR_r16__cond a -> SidelinkPreconfigNR_r16__list_cond (SidelinkPreconfigNR_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SidelinkPreconfigNR_r16__helper2 : (forall a : SidelinkPreconfigNR_r16__Type, SidelinkPreconfigNR_r16__F2 (SidelinkPreconfigNR_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SidelinkPreconfigNR_r16__helper3 : (forall b : SidelinkPreconfigNR_r16__list_type, SidelinkPreconfigNR_r16__list_cond b -> SidelinkPreconfigNR_r16__cond (SidelinkPreconfigNR_r16__F2 b) /\ SidelinkPreconfigNR_r16__F1 (SidelinkPreconfigNR_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SidelinkPreconfigNR_r16__cond, SidelinkPreconfigNR_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SidelinkPreconfigNR_r16__Format : T_Format SidelinkPreconfigNR_r16__Type SidelinkPreconfigNR_r16__cond :=
 proj2_format SidelinkPreconfigNR_r16__cond SidelinkPreconfigNR_r16__list_format  SidelinkPreconfigNR_r16__F1 SidelinkPreconfigNR_r16__F2 SidelinkPreconfigNR_r16__helper1 SidelinkPreconfigNR_r16__helper2 SidelinkPreconfigNR_r16__helper3.

Opaque SidelinkPreconfigNR_r16__cond SidelinkPreconfigNR_r16__Format.

