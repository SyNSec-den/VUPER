Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_ConfigIndexCG_r16.

Opaque SL_ConfigIndexCG_r16__cond SL_ConfigIndexCG_r16__Format.

Require Import NR.SL_PeriodCG_r16.

Opaque SL_PeriodCG_r16__cond SL_PeriodCG_r16__Format.

Lemma SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__Type := Z.
Definition SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__cond := (fun z => (1 <= z <= 16)%Z).
Lemma SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__Type := Z.
Definition SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__cond := (fun z => (0 <= z <= 15)%Z).
Require Import NR.SL_CG_MaxTransNumList_r16.

Opaque SL_CG_MaxTransNumList_r16__cond SL_CG_MaxTransNumList_r16__Format.

Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__helper1 : (0 <= 496)%Z.  lia. Qed.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__helper2 : to_bit_sz (Z.to_nat (496 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (496 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__Type := Z.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__cond := (fun z => (0 <= z <= 496)%Z).
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__helper1 : (0 <= 26)%Z.  lia. Qed.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__helper2 : to_bit_sz (Z.to_nat (26 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (26 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__Type := Z.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__cond := (fun z => (0 <= z <= 26)%Z).
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__helper1 : (0 <= 6929)%Z.  lia. Qed.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__helper2 : to_bit_sz (Z.to_nat (6929 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6929 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__Type := Z.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__cond := (fun z => (0 <= z <= 6929)%Z).
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__helper1 : (0 <= 7999)%Z.  lia. Qed.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__helper2 : to_bit_sz (Z.to_nat (7999 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7999 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__Type := Z.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__cond := (fun z => (0 <= z <= 7999)%Z).
Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__Type := Z.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__cond := (fun z => (0 <= z <= 15)%Z).
Require Import NR.SL_ResourcePoolID_r16.

Opaque SL_ResourcePoolID_r16__cond SL_ResourcePoolID_r16__Format.

Inductive SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Type : Set :=
 | SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__sfn512
.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__cond := (fun (_ : SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Type) => True).
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__nat__helper.

Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F1 t :=
  match t with
  | SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__sfn512 => 0
  end.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F2 n :=
  match n with
  | 0 => SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__sfn512
  | _ => SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__sfn512
  end.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F1F2 : forall x : SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Type, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F1 x <= 0) /\ SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F2 (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F1 (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F2 y) = y. enum_solve H y. Qed.

Record SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Type : Set :=
  make__SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Type {
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16 : option Z ;
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16 : option Z ;
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16 : option Z ;
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16 : option Z ;
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_N1PUCCH_AN_r16 : option PUCCH_ResourceId__Type ;
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16 : option Z ;
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_ResourcePoolID_r16 : option SL_ResourcePoolID_r16__Type ;
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16 : option SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Type ;
}.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list := (
 Opt Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__cond ::
 Opt Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__cond ::
 Opt Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__cond ::
 Opt Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__cond ::
 Opt PUCCH_ResourceId__Type PUCCH_ResourceId__cond ::
 Opt Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__cond ::
 Opt SL_ResourcePoolID_r16__Type SL_ResourcePoolID_r16__cond ::
 Opt SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Type SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__cond ::
 nil).
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond z := 
  opt_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16 z) /\
  opt_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16 z) /\
  opt_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16 z) /\
  opt_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16 z) /\
  opt_cond PUCCH_ResourceId__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_N1PUCCH_AN_r16 z) /\
  opt_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16 z) /\
  opt_cond SL_ResourcePoolID_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_ResourcePoolID_r16 z) /\
  opt_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16 z) /\
  True.

Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Record SL_ConfiguredGrantConfig_r16__ext0O__Type : Set :=
  make__SL_ConfiguredGrantConfig_r16__ext0O__Type {
    SL_ConfiguredGrantConfig_r16__ext0O__sl_N1PUCCH_AN_Type2_r16 : option PUCCH_ResourceId__Type ;
}.
Definition SL_ConfiguredGrantConfig_r16__ext0O__list := (
 Opt PUCCH_ResourceId__Type PUCCH_ResourceId__cond ::
 nil).
Definition SL_ConfiguredGrantConfig_r16__ext0O__cond z := 
  opt_cond PUCCH_ResourceId__cond (SL_ConfiguredGrantConfig_r16__ext0O__sl_N1PUCCH_AN_Type2_r16 z) /\
  True.

Definition SL_ConfiguredGrantConfig_r16__ext0__Type := SL_ConfiguredGrantConfig_r16__ext0O__Type.
Definition SL_ConfiguredGrantConfig_r16__ext0__cond := SL_ConfiguredGrantConfig_r16__ext0O__cond.

Record SL_ConfiguredGrantConfig_r16__Type : Set :=
  make__SL_ConfiguredGrantConfig_r16__Type {
    SL_ConfiguredGrantConfig_r16__sl_ConfigIndexCG_r16 : SL_ConfigIndexCG_r16__Type ;
    SL_ConfiguredGrantConfig_r16__sl_PeriodCG_r16 : option SL_PeriodCG_r16__Type ;
    SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16 : option Z ;
    SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16 : option Z ;
    SL_ConfiguredGrantConfig_r16__sl_CG_MaxTransNumList_r16 : option SL_CG_MaxTransNumList_r16__Type ;
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16 : option SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Type ;
    SL_ConfiguredGrantConfig_r16__ext0 : option SL_ConfiguredGrantConfig_r16__ext0__Type ;
}.
Definition SL_ConfiguredGrantConfig_r16__root_list : list seq_elem := (
 Nor SL_ConfigIndexCG_r16__Type SL_ConfigIndexCG_r16__cond ::
 Opt SL_PeriodCG_r16__Type SL_PeriodCG_r16__cond ::
 Opt Z SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__cond ::
 Opt Z SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__cond ::
 Opt SL_CG_MaxTransNumList_r16__Type SL_CG_MaxTransNumList_r16__cond ::
 Opt SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Type SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond ::
 nil).
Definition SL_ConfiguredGrantConfig_r16__ext_list : list typ := (
  typ_cons SL_ConfiguredGrantConfig_r16__ext0__Type SL_ConfiguredGrantConfig_r16__ext0__cond ::
  nil).
Definition SL_ConfiguredGrantConfig_r16__cond (z : SL_ConfiguredGrantConfig_r16__Type) := 
(  SL_ConfigIndexCG_r16__cond (SL_ConfiguredGrantConfig_r16__sl_ConfigIndexCG_r16 z) /\
  opt_cond SL_PeriodCG_r16__cond (SL_ConfiguredGrantConfig_r16__sl_PeriodCG_r16 z) /\
  opt_cond SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__cond (SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16 z) /\
  opt_cond SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__cond (SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16 z) /\
  opt_cond SL_CG_MaxTransNumList_r16__cond (SL_ConfiguredGrantConfig_r16__sl_CG_MaxTransNumList_r16 z) /\
  opt_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16 z) /\
  True) /\ 
(  opt_cond SL_ConfiguredGrantConfig_r16__ext0__cond (SL_ConfiguredGrantConfig_r16__ext0 z) /\
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
Definition SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__Format : T_Format Z SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__cond :=
 ranged_int_format (1) (16) SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__helper1 SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__helper2.

Opaque SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__cond SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__Format.

Definition SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__Format : T_Format Z SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__cond :=
 ranged_int_format (0) (15) SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__helper1 SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__helper2.

Opaque SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__cond SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__Format.

Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__Format : T_Format Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__cond :=
 ranged_int_format (0) (496) SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__helper1 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__helper2.

Opaque SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__Format.

Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__Format : T_Format Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__cond :=
 ranged_int_format (0) (26) SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__helper1 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__helper2.

Opaque SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__Format.

Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__Format : T_Format Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__cond :=
 ranged_int_format (0) (6929) SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__helper1 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__helper2.

Opaque SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__Format.

Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__Format : T_Format Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__cond :=
 ranged_int_format (0) (7999) SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__helper1 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__helper2.

Opaque SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__Format.

Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__Format : T_Format Z SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__cond :=
 ranged_int_format (0) (15) SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__helper1 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__helper2.

Opaque SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__Format.

Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Format : T_Format SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__nat__Format SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F1 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F2 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F1F2 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__F2F1.

Opaque SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Format.


Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Format_Type := Eval cbn in seq_format_prod SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Format_list : SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Format_Type :=
  (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16__Format, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16__Format, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16__Format, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16__Format, (PUCCH_ResourceId__Format, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16__Format, (SL_ResourcePoolID_r16__Format, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16__Format, unit_format)))))))).
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list__Format := (*Eval compute in *) seq_format SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Format_list.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1 z :=
  (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeResourceCG_Type1_r16 z, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_StartSubchannelCG_Type1_r16 z, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_FreqResourceCG_Type1_r16 z, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeOffsetCG_Type1_r16 z, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_N1PUCCH_AN_r16 z, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_PSFCH_ToPUCCH_CG_Type1_r16 z, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_ResourcePoolID_r16 z, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__sl_TimeReferenceSFN_Type1_r16 z, tt)))))))).
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F2 (y : seq_type SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1F2_cond (z : SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Type)
  : SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond z ->
  (seq_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1 z)).
intro H. unfold SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond in H. simpl. auto. Qed.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1F2_cond2 (z : SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Type)
 : SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F2 (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F2F1_cond (y : seq_type SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list)
  : seq_cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list y ->
 (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F2 y)) /\  SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1 (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond. simpl in *. auto.
 - simpl. unfold SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Format : T_Format SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Type SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond :=
        proj2_format  SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__list__Format
    SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F2 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1F2_cond  SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F1F2_cond2 SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__F2F1_cond.
Opaque SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__cond SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Format.


Definition SL_ConfiguredGrantConfig_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SL_ConfiguredGrantConfig_r16__ext0O__list.
Definition SL_ConfiguredGrantConfig_r16__ext0O__Format_list : SL_ConfiguredGrantConfig_r16__ext0O__Format_Type :=
  (PUCCH_ResourceId__Format, unit_format).
Definition SL_ConfiguredGrantConfig_r16__ext0O__list__Format := (*Eval compute in *) seq_format SL_ConfiguredGrantConfig_r16__ext0O__list SL_ConfiguredGrantConfig_r16__ext0O__Format_list.
Definition SL_ConfiguredGrantConfig_r16__ext0O__F1 z :=
  (SL_ConfiguredGrantConfig_r16__ext0O__sl_N1PUCCH_AN_Type2_r16 z, tt).
Definition SL_ConfiguredGrantConfig_r16__ext0O__F2 (y : seq_type SL_ConfiguredGrantConfig_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SL_ConfiguredGrantConfig_r16__ext0O__Type i0
  end.
Lemma SL_ConfiguredGrantConfig_r16__ext0O__F1F2_cond (z : SL_ConfiguredGrantConfig_r16__ext0O__Type)
  : SL_ConfiguredGrantConfig_r16__ext0O__cond z ->
  (seq_cond SL_ConfiguredGrantConfig_r16__ext0O__list (SL_ConfiguredGrantConfig_r16__ext0O__F1 z)).
intro H. unfold SL_ConfiguredGrantConfig_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SL_ConfiguredGrantConfig_r16__ext0O__F1F2_cond2 (z : SL_ConfiguredGrantConfig_r16__ext0O__Type)
 : SL_ConfiguredGrantConfig_r16__ext0O__F2 (SL_ConfiguredGrantConfig_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_ConfiguredGrantConfig_r16__ext0O__F2F1_cond (y : seq_type SL_ConfiguredGrantConfig_r16__ext0O__list)
  : seq_cond SL_ConfiguredGrantConfig_r16__ext0O__list y ->
 (SL_ConfiguredGrantConfig_r16__ext0O__cond (SL_ConfiguredGrantConfig_r16__ext0O__F2 y)) /\  SL_ConfiguredGrantConfig_r16__ext0O__F1 (SL_ConfiguredGrantConfig_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_ConfiguredGrantConfig_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SL_ConfiguredGrantConfig_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_ConfiguredGrantConfig_r16__ext0O__Format : T_Format SL_ConfiguredGrantConfig_r16__ext0O__Type SL_ConfiguredGrantConfig_r16__ext0O__cond :=
        proj2_format  SL_ConfiguredGrantConfig_r16__ext0O__cond SL_ConfiguredGrantConfig_r16__ext0O__list__Format
    SL_ConfiguredGrantConfig_r16__ext0O__F1 SL_ConfiguredGrantConfig_r16__ext0O__F2 SL_ConfiguredGrantConfig_r16__ext0O__F1F2_cond  SL_ConfiguredGrantConfig_r16__ext0O__F1F2_cond2 SL_ConfiguredGrantConfig_r16__ext0O__F2F1_cond.
Opaque SL_ConfiguredGrantConfig_r16__ext0O__cond SL_ConfiguredGrantConfig_r16__ext0O__Format.

Definition SL_ConfiguredGrantConfig_r16__ext0__check_all_none (b : SL_ConfiguredGrantConfig_r16__ext0O__Type) : bool :=
match b with 
  | make__SL_ConfiguredGrantConfig_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SL_ConfiguredGrantConfig_r16__ext0__Format : T_Format SL_ConfiguredGrantConfig_r16__ext0__Type SL_ConfiguredGrantConfig_r16__ext0__cond :=
  restrict_add_format SL_ConfiguredGrantConfig_r16__ext0__check_all_none SL_ConfiguredGrantConfig_r16__ext0O__Format.

Opaque SL_ConfiguredGrantConfig_r16__ext0__cond SL_ConfiguredGrantConfig_r16__ext0__Format.


Definition SL_ConfiguredGrantConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_ConfiguredGrantConfig_r16__root_list.
Definition SL_ConfiguredGrantConfig_r16__root_Format_list : SL_ConfiguredGrantConfig_r16__root_Format_Type :=
  (SL_ConfigIndexCG_r16__Format, (SL_PeriodCG_r16__Format, (SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16__Format, (SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16__Format, (SL_CG_MaxTransNumList_r16__Format, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16__Format, unit_format)))))).

Definition SL_ConfiguredGrantConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_ConfiguredGrantConfig_r16__ext_list.
Definition SL_ConfiguredGrantConfig_r16__ext_Format_list : SL_ConfiguredGrantConfig_r16__ext_Format_Type :=
  (SL_ConfiguredGrantConfig_r16__ext0__Format, unit__Format).

Definition SL_ConfiguredGrantConfig_r16__list_type : Set := (seq_type SL_ConfiguredGrantConfig_r16__root_list) * (seq_ext_type SL_ConfiguredGrantConfig_r16__ext_list).
Definition SL_ConfiguredGrantConfig_r16__list_cond (z : SL_ConfiguredGrantConfig_r16__list_type) : Prop :=
        (seq_cond SL_ConfiguredGrantConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_ConfiguredGrantConfig_r16__ext_list (snd z)).
Definition SL_ConfiguredGrantConfig_r16__list_format : T_Format SL_ConfiguredGrantConfig_r16__list_type SL_ConfiguredGrantConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_ConfiguredGrantConfig_r16__root_list SL_ConfiguredGrantConfig_r16__root_Format_list SL_ConfiguredGrantConfig_r16__ext_list SL_ConfiguredGrantConfig_r16__ext_Format_list.

Opaque SL_ConfiguredGrantConfig_r16__list_format.
Definition SL_ConfiguredGrantConfig_r16__F1 (z : SL_ConfiguredGrantConfig_r16__Type) : SL_ConfiguredGrantConfig_r16__list_type :=
  (((SL_ConfiguredGrantConfig_r16__sl_ConfigIndexCG_r16 z, (SL_ConfiguredGrantConfig_r16__sl_PeriodCG_r16 z, (SL_ConfiguredGrantConfig_r16__sl_NrOfHARQ_Processes_r16 z, (SL_ConfiguredGrantConfig_r16__sl_HARQ_ProcID_offset_r16 z, (SL_ConfiguredGrantConfig_r16__sl_CG_MaxTransNumList_r16 z, (SL_ConfiguredGrantConfig_r16__rrc_ConfiguredSidelinkGrant_r16 z, tt))))))), (
(SL_ConfiguredGrantConfig_r16__ext0 z, tt))).
Definition SL_ConfiguredGrantConfig_r16__F2 (y : SL_ConfiguredGrantConfig_r16__list_type) : SL_ConfiguredGrantConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, _))=>
    make__SL_ConfiguredGrantConfig_r16__Type j0 j1 j2 j3 j4 j5 i0
  end.
Definition SL_ConfiguredGrantConfig_r16__helper1 : (forall a : SL_ConfiguredGrantConfig_r16__Type, SL_ConfiguredGrantConfig_r16__cond a -> SL_ConfiguredGrantConfig_r16__list_cond (SL_ConfiguredGrantConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_ConfiguredGrantConfig_r16__helper2 : (forall a : SL_ConfiguredGrantConfig_r16__Type, SL_ConfiguredGrantConfig_r16__F2 (SL_ConfiguredGrantConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_ConfiguredGrantConfig_r16__helper3 : (forall b : SL_ConfiguredGrantConfig_r16__list_type, SL_ConfiguredGrantConfig_r16__list_cond b -> SL_ConfiguredGrantConfig_r16__cond (SL_ConfiguredGrantConfig_r16__F2 b) /\ SL_ConfiguredGrantConfig_r16__F1 (SL_ConfiguredGrantConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_ConfiguredGrantConfig_r16__cond, SL_ConfiguredGrantConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_ConfiguredGrantConfig_r16__Format : T_Format SL_ConfiguredGrantConfig_r16__Type SL_ConfiguredGrantConfig_r16__cond :=
 proj2_format SL_ConfiguredGrantConfig_r16__cond SL_ConfiguredGrantConfig_r16__list_format  SL_ConfiguredGrantConfig_r16__F1 SL_ConfiguredGrantConfig_r16__F2 SL_ConfiguredGrantConfig_r16__helper1 SL_ConfiguredGrantConfig_r16__helper2 SL_ConfiguredGrantConfig_r16__helper3.

Opaque SL_ConfiguredGrantConfig_r16__cond SL_ConfiguredGrantConfig_r16__Format.

