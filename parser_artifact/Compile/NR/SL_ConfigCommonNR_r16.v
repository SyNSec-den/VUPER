Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_FreqConfigCommon_r16.

Opaque SL_FreqConfigCommon_r16__cond SL_FreqConfigCommon_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__Type := list SL_FreqConfigCommon_r16__Type.

Lemma SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__helper1 : (0 <= 1 <= maxNrofFreqSL_r16)%Z. unfold maxNrofFreqSL_r16.
 lia. Qed.
Lemma SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofFreqSL_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofFreqSL_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__cond (z : SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofFreqSL_r16)%Z /\ (list_and SL_FreqConfigCommon_r16__cond z) .

Require Import NR.SL_UE_SelectedConfig_r16.

Opaque SL_UE_SelectedConfig_r16__cond SL_UE_SelectedConfig_r16__Format.

Require Import NR.SL_NR_AnchorCarrierFreqList_r16.

Opaque SL_NR_AnchorCarrierFreqList_r16__cond SL_NR_AnchorCarrierFreqList_r16__Format.

Require Import NR.SL_EUTRA_AnchorCarrierFreqList_r16.

Opaque SL_EUTRA_AnchorCarrierFreqList_r16__cond SL_EUTRA_AnchorCarrierFreqList_r16__Format.

Require Import NR.SL_RadioBearerConfig_r16.

Opaque SL_RadioBearerConfig_r16__cond SL_RadioBearerConfig_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__Type := list SL_RadioBearerConfig_r16__Type.

Lemma SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__helper1 : (0 <= 1 <= maxNrofSLRB_r16)%Z. unfold maxNrofSLRB_r16.
 lia. Qed.
Lemma SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSLRB_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSLRB_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__cond (z : SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSLRB_r16)%Z /\ (list_and SL_RadioBearerConfig_r16__cond z) .

Require Import NR.SL_RLC_BearerConfig_r16.

Opaque SL_RLC_BearerConfig_r16__cond SL_RLC_BearerConfig_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__Type := list SL_RLC_BearerConfig_r16__Type.

Lemma SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__helper1 : (0 <= 1 <= maxSL_LCID_r16)%Z. unfold maxSL_LCID_r16.
 lia. Qed.
Lemma SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__helper2 : to_bit_sz (Z.to_nat (maxSL_LCID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSL_LCID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__cond (z : SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSL_LCID_r16)%Z /\ (list_and SL_RLC_BearerConfig_r16__cond z) .

Require Import NR.SL_MeasConfigCommon_r16.

Opaque SL_MeasConfigCommon_r16__cond SL_MeasConfigCommon_r16__Format.

Inductive SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Type : Set :=
 | SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__enabled
.
Definition SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__cond := (fun (_ : SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Type) => True).
Lemma SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__nat__helper.

Definition SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F1 t :=
  match t with
  | SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__enabled => 0
  end.
Definition SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F2 n :=
  match n with
  | 0 => SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__enabled
  | _ => SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__enabled
  end.
Lemma SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F1F2 : forall x : SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Type, (SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F1 x <= 0) /\ SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F2 (SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F1 (SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__helper1 : (1 <= 1000)%Z.  lia. Qed.
Lemma SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__helper2 : to_bit_sz (Z.to_nat (1000 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1000 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__Type := Z.
Definition SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__cond := (fun z => (1 <= z <= 1000)%Z).
Inductive SL_ConfigCommonNR_r16__t400_r16__Type : Set :=
 | SL_ConfigCommonNR_r16__t400_r16__ms100
 | SL_ConfigCommonNR_r16__t400_r16__ms200
 | SL_ConfigCommonNR_r16__t400_r16__ms300
 | SL_ConfigCommonNR_r16__t400_r16__ms400
 | SL_ConfigCommonNR_r16__t400_r16__ms600
 | SL_ConfigCommonNR_r16__t400_r16__ms1000
 | SL_ConfigCommonNR_r16__t400_r16__ms1500
 | SL_ConfigCommonNR_r16__t400_r16__ms2000
.
Definition SL_ConfigCommonNR_r16__t400_r16__cond := (fun (_ : SL_ConfigCommonNR_r16__t400_r16__Type) => True).
Lemma SL_ConfigCommonNR_r16__t400_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ConfigCommonNR_r16__t400_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_ConfigCommonNR_r16__t400_r16__nat__helper.

Definition SL_ConfigCommonNR_r16__t400_r16__F1 t :=
  match t with
  | SL_ConfigCommonNR_r16__t400_r16__ms100 => 0
  | SL_ConfigCommonNR_r16__t400_r16__ms200 => 1
  | SL_ConfigCommonNR_r16__t400_r16__ms300 => 2
  | SL_ConfigCommonNR_r16__t400_r16__ms400 => 3
  | SL_ConfigCommonNR_r16__t400_r16__ms600 => 4
  | SL_ConfigCommonNR_r16__t400_r16__ms1000 => 5
  | SL_ConfigCommonNR_r16__t400_r16__ms1500 => 6
  | SL_ConfigCommonNR_r16__t400_r16__ms2000 => 7
  end.
Definition SL_ConfigCommonNR_r16__t400_r16__F2 n :=
  match n with
  | 0 => SL_ConfigCommonNR_r16__t400_r16__ms100
  | 1 => SL_ConfigCommonNR_r16__t400_r16__ms200
  | 2 => SL_ConfigCommonNR_r16__t400_r16__ms300
  | 3 => SL_ConfigCommonNR_r16__t400_r16__ms400
  | 4 => SL_ConfigCommonNR_r16__t400_r16__ms600
  | 5 => SL_ConfigCommonNR_r16__t400_r16__ms1000
  | 6 => SL_ConfigCommonNR_r16__t400_r16__ms1500
  | 7 => SL_ConfigCommonNR_r16__t400_r16__ms2000
  | _ => SL_ConfigCommonNR_r16__t400_r16__ms100
  end.
Lemma SL_ConfigCommonNR_r16__t400_r16__F1F2 : forall x : SL_ConfigCommonNR_r16__t400_r16__Type, (SL_ConfigCommonNR_r16__t400_r16__F1 x <= 7) /\ SL_ConfigCommonNR_r16__t400_r16__F2 (SL_ConfigCommonNR_r16__t400_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ConfigCommonNR_r16__t400_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_ConfigCommonNR_r16__t400_r16__F1 (SL_ConfigCommonNR_r16__t400_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Type : Set :=
 | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n1
 | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n2
 | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n3
 | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n4
 | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n6
 | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n8
 | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n16
 | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n32
.
Definition SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__cond := (fun (_ : SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Type) => True).
Lemma SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__nat__helper.

Definition SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 t :=
  match t with
  | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n1 => 0
  | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n2 => 1
  | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n3 => 2
  | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n4 => 3
  | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n6 => 4
  | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n8 => 5
  | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n16 => 6
  | SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n32 => 7
  end.
Definition SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F2 n :=
  match n with
  | 0 => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n1
  | 1 => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n2
  | 2 => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n3
  | 3 => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n4
  | 4 => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n6
  | 5 => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n8
  | 6 => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n16
  | 7 => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n32
  | _ => SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__n1
  end.
Lemma SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F1F2 : forall x : SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Type, (SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 x <= 7) /\ SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F2 (SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 (SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__Type := Z.
Definition SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__cond := (fun z => (1 <= z <= 8)%Z).
Record SL_ConfigCommonNR_r16__Type : Set :=
  make__SL_ConfigCommonNR_r16__Type {
    SL_ConfigCommonNR_r16__sl_FreqInfoList_r16 : option SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__Type ;
    SL_ConfigCommonNR_r16__sl_UE_SelectedConfig_r16 : option SL_UE_SelectedConfig_r16__Type ;
    SL_ConfigCommonNR_r16__sl_NR_AnchorCarrierFreqList_r16 : option SL_NR_AnchorCarrierFreqList_r16__Type ;
    SL_ConfigCommonNR_r16__sl_EUTRA_AnchorCarrierFreqList_r16 : option SL_EUTRA_AnchorCarrierFreqList_r16__Type ;
    SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16 : option SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__Type ;
    SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16 : option SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__Type ;
    SL_ConfigCommonNR_r16__sl_MeasConfigCommon_r16 : option SL_MeasConfigCommon_r16__Type ;
    SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16 : option SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Type ;
    SL_ConfigCommonNR_r16__sl_OffsetDFN_r16 : option Z ;
    SL_ConfigCommonNR_r16__t400_r16 : option SL_ConfigCommonNR_r16__t400_r16__Type ;
    SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16 : option SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Type ;
    SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16 : option Z ;
}.
Definition SL_ConfigCommonNR_r16__list := (
 Opt SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__Type SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__cond ::
 Opt SL_UE_SelectedConfig_r16__Type SL_UE_SelectedConfig_r16__cond ::
 Opt SL_NR_AnchorCarrierFreqList_r16__Type SL_NR_AnchorCarrierFreqList_r16__cond ::
 Opt SL_EUTRA_AnchorCarrierFreqList_r16__Type SL_EUTRA_AnchorCarrierFreqList_r16__cond ::
 Opt SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__Type SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__cond ::
 Opt SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__Type SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__cond ::
 Opt SL_MeasConfigCommon_r16__Type SL_MeasConfigCommon_r16__cond ::
 Opt SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Type SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__cond ::
 Opt Z SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__cond ::
 Opt SL_ConfigCommonNR_r16__t400_r16__Type SL_ConfigCommonNR_r16__t400_r16__cond ::
 Opt SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Type SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__cond ::
 Opt Z SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__cond ::
 nil).
Definition SL_ConfigCommonNR_r16__cond z := 
  opt_cond SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__cond (SL_ConfigCommonNR_r16__sl_FreqInfoList_r16 z) /\
  opt_cond SL_UE_SelectedConfig_r16__cond (SL_ConfigCommonNR_r16__sl_UE_SelectedConfig_r16 z) /\
  opt_cond SL_NR_AnchorCarrierFreqList_r16__cond (SL_ConfigCommonNR_r16__sl_NR_AnchorCarrierFreqList_r16 z) /\
  opt_cond SL_EUTRA_AnchorCarrierFreqList_r16__cond (SL_ConfigCommonNR_r16__sl_EUTRA_AnchorCarrierFreqList_r16 z) /\
  opt_cond SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__cond (SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16 z) /\
  opt_cond SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__cond (SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16 z) /\
  opt_cond SL_MeasConfigCommon_r16__cond (SL_ConfigCommonNR_r16__sl_MeasConfigCommon_r16 z) /\
  opt_cond SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__cond (SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16 z) /\
  opt_cond SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__cond (SL_ConfigCommonNR_r16__sl_OffsetDFN_r16 z) /\
  opt_cond SL_ConfigCommonNR_r16__t400_r16__cond (SL_ConfigCommonNR_r16__t400_r16 z) /\
  opt_cond SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__cond (SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16 z) /\
  opt_cond SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__cond (SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16 z) /\
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
Definition SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__Format : T_Format SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__Type SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__cond := seq_of_format SL_FreqConfigCommon_r16__Format 1 maxNrofFreqSL_r16 SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__helper1 SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__helper2.

Opaque SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__cond SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__Format : T_Format SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__Type SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__cond := seq_of_format SL_RadioBearerConfig_r16__Format 1 maxNrofSLRB_r16 SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__helper1 SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__helper2.

Opaque SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__cond SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__Format : T_Format SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__Type SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__cond := seq_of_format SL_RLC_BearerConfig_r16__Format 1 maxSL_LCID_r16 SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__helper1 SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__helper2.

Opaque SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__cond SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Format : T_Format SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__nat__Format SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F1 SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F2 SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F1F2 SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__F2F1.

Opaque SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__cond SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__Format : T_Format Z SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__cond :=
 ranged_int_format (1) (1000) SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__helper1 SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__helper2.

Opaque SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__cond SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__Format.

Definition SL_ConfigCommonNR_r16__t400_r16__Format : T_Format SL_ConfigCommonNR_r16__t400_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ConfigCommonNR_r16__t400_r16__nat__Format SL_ConfigCommonNR_r16__t400_r16__F1 SL_ConfigCommonNR_r16__t400_r16__F2 SL_ConfigCommonNR_r16__t400_r16__F1F2 SL_ConfigCommonNR_r16__t400_r16__F2F1.

Opaque SL_ConfigCommonNR_r16__t400_r16__cond SL_ConfigCommonNR_r16__t400_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Format : T_Format SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__nat__Format SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F1 SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F2 SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F1F2 SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__F2F1.

Opaque SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__cond SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Format.

Definition SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__Format : T_Format Z SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__cond :=
 ranged_int_format (1) (8) SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__helper1 SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__helper2.

Opaque SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__cond SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__Format.


Definition SL_ConfigCommonNR_r16__Format_Type := Eval cbn in seq_format_prod SL_ConfigCommonNR_r16__list.
Definition SL_ConfigCommonNR_r16__Format_list : SL_ConfigCommonNR_r16__Format_Type :=
  (SL_ConfigCommonNR_r16__sl_FreqInfoList_r16__Format, (SL_UE_SelectedConfig_r16__Format, (SL_NR_AnchorCarrierFreqList_r16__Format, (SL_EUTRA_AnchorCarrierFreqList_r16__Format, (SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16__Format, (SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16__Format, (SL_MeasConfigCommon_r16__Format, (SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16__Format, (SL_ConfigCommonNR_r16__sl_OffsetDFN_r16__Format, (SL_ConfigCommonNR_r16__t400_r16__Format, (SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16__Format, (SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16__Format, unit_format)))))))))))).
Definition SL_ConfigCommonNR_r16__list__Format := (*Eval compute in *) seq_format SL_ConfigCommonNR_r16__list SL_ConfigCommonNR_r16__Format_list.
Definition SL_ConfigCommonNR_r16__F1 z :=
  (SL_ConfigCommonNR_r16__sl_FreqInfoList_r16 z, (SL_ConfigCommonNR_r16__sl_UE_SelectedConfig_r16 z, (SL_ConfigCommonNR_r16__sl_NR_AnchorCarrierFreqList_r16 z, (SL_ConfigCommonNR_r16__sl_EUTRA_AnchorCarrierFreqList_r16 z, (SL_ConfigCommonNR_r16__sl_RadioBearerConfigList_r16 z, (SL_ConfigCommonNR_r16__sl_RLC_BearerConfigList_r16 z, (SL_ConfigCommonNR_r16__sl_MeasConfigCommon_r16 z, (SL_ConfigCommonNR_r16__sl_CSI_Acquisition_r16 z, (SL_ConfigCommonNR_r16__sl_OffsetDFN_r16 z, (SL_ConfigCommonNR_r16__t400_r16 z, (SL_ConfigCommonNR_r16__sl_MaxNumConsecutiveDTX_r16 z, (SL_ConfigCommonNR_r16__sl_SSB_PriorityNR_r16 z, tt)))))))))))).
Definition SL_ConfigCommonNR_r16__F2 (y : seq_type SL_ConfigCommonNR_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, _))))))))))))=>
    make__SL_ConfigCommonNR_r16__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  end.
Lemma SL_ConfigCommonNR_r16__F1F2_cond (z : SL_ConfigCommonNR_r16__Type)
  : SL_ConfigCommonNR_r16__cond z ->
  (seq_cond SL_ConfigCommonNR_r16__list (SL_ConfigCommonNR_r16__F1 z)).
intro H. unfold SL_ConfigCommonNR_r16__cond in H. simpl. auto. Qed.
Lemma SL_ConfigCommonNR_r16__F1F2_cond2 (z : SL_ConfigCommonNR_r16__Type)
 : SL_ConfigCommonNR_r16__F2 (SL_ConfigCommonNR_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_ConfigCommonNR_r16__F2F1_cond (y : seq_type SL_ConfigCommonNR_r16__list)
  : seq_cond SL_ConfigCommonNR_r16__list y ->
 (SL_ConfigCommonNR_r16__cond (SL_ConfigCommonNR_r16__F2 y)) /\  SL_ConfigCommonNR_r16__F1 (SL_ConfigCommonNR_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_ConfigCommonNR_r16__cond. simpl in *. auto.
 - simpl. unfold SL_ConfigCommonNR_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_ConfigCommonNR_r16__Format : T_Format SL_ConfigCommonNR_r16__Type SL_ConfigCommonNR_r16__cond :=
        proj2_format  SL_ConfigCommonNR_r16__cond SL_ConfigCommonNR_r16__list__Format
    SL_ConfigCommonNR_r16__F1 SL_ConfigCommonNR_r16__F2 SL_ConfigCommonNR_r16__F1F2_cond  SL_ConfigCommonNR_r16__F1F2_cond2 SL_ConfigCommonNR_r16__F2F1_cond.
Opaque SL_ConfigCommonNR_r16__cond SL_ConfigCommonNR_r16__Format.

