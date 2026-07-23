Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma BeamFailureRecoveryConfig__rootSequenceIndex_BFR__helper1 : (0 <= 137)%Z.  lia. Qed.
Lemma BeamFailureRecoveryConfig__rootSequenceIndex_BFR__helper2 : to_bit_sz (Z.to_nat (137 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (137 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BeamFailureRecoveryConfig__rootSequenceIndex_BFR__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BeamFailureRecoveryConfig__rootSequenceIndex_BFR__Type := Z.
Definition BeamFailureRecoveryConfig__rootSequenceIndex_BFR__cond := (fun z => (0 <= z <= 137)%Z).
Require Import NR.RACH_ConfigGeneric.

Opaque RACH_ConfigGeneric__cond RACH_ConfigGeneric__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.PRACH_ResourceDedicatedBFR.

Opaque PRACH_ResourceDedicatedBFR__cond PRACH_ResourceDedicatedBFR__Format.

Definition BeamFailureRecoveryConfig__candidateBeamRSList__Type := list PRACH_ResourceDedicatedBFR__Type.

Lemma BeamFailureRecoveryConfig__candidateBeamRSList__helper1 : (0 <= 1 <= maxNrofCandidateBeams)%Z. unfold maxNrofCandidateBeams.
 lia. Qed.
Lemma BeamFailureRecoveryConfig__candidateBeamRSList__helper2 : to_bit_sz (Z.to_nat (maxNrofCandidateBeams - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCandidateBeams - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BeamFailureRecoveryConfig__candidateBeamRSList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BeamFailureRecoveryConfig__candidateBeamRSList__cond (z : BeamFailureRecoveryConfig__candidateBeamRSList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCandidateBeams)%Z /\ (list_and PRACH_ResourceDedicatedBFR__cond z) .

Inductive BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Type : Set :=
 | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneEighth
 | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneFourth
 | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneHalf
 | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__one
 | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__two
 | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__four
 | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__eight
 | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__sixteen
.
Definition BeamFailureRecoveryConfig__ssb_perRACH_Occasion__cond := (fun (_ : BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Type) => True).
Lemma BeamFailureRecoveryConfig__ssb_perRACH_Occasion__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamFailureRecoveryConfig__ssb_perRACH_Occasion__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 BeamFailureRecoveryConfig__ssb_perRACH_Occasion__nat__helper.

Definition BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F1 t :=
  match t with
  | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneEighth => 0
  | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneFourth => 1
  | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneHalf => 2
  | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__one => 3
  | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__two => 4
  | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__four => 5
  | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__eight => 6
  | BeamFailureRecoveryConfig__ssb_perRACH_Occasion__sixteen => 7
  end.
Definition BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F2 n :=
  match n with
  | 0 => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneEighth
  | 1 => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneFourth
  | 2 => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneHalf
  | 3 => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__one
  | 4 => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__two
  | 5 => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__four
  | 6 => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__eight
  | 7 => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__sixteen
  | _ => BeamFailureRecoveryConfig__ssb_perRACH_Occasion__oneEighth
  end.
Lemma BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F1F2 : forall x : BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Type, (BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F1 x <= 7) /\ BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F2 (BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F1 x) = x. imp_solve. Qed.
Lemma BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F2F1 : forall (y : nat) (H : y <= 7), BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F1 (BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F2 y) = y. enum_solve H y. Qed.

Lemma BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__Type := Z.
Definition BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__cond := (fun z => (0 <= z <= 15)%Z).
Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Require Import NR.RA_Prioritization.

Opaque RA_Prioritization__cond RA_Prioritization__Format.

Inductive BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Type : Set :=
 | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms10
 | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms20
 | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms40
 | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms60
 | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms80
 | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms100
 | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms150
 | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms200
.
Definition BeamFailureRecoveryConfig__beamFailureRecoveryTimer__cond := (fun (_ : BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Type) => True).
Lemma BeamFailureRecoveryConfig__beamFailureRecoveryTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamFailureRecoveryConfig__beamFailureRecoveryTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 BeamFailureRecoveryConfig__beamFailureRecoveryTimer__nat__helper.

Definition BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F1 t :=
  match t with
  | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms10 => 0
  | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms20 => 1
  | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms40 => 2
  | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms60 => 3
  | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms80 => 4
  | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms100 => 5
  | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms150 => 6
  | BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms200 => 7
  end.
Definition BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F2 n :=
  match n with
  | 0 => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms10
  | 1 => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms20
  | 2 => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms40
  | 3 => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms60
  | 4 => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms80
  | 5 => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms100
  | 6 => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms150
  | 7 => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms200
  | _ => BeamFailureRecoveryConfig__beamFailureRecoveryTimer__ms10
  end.
Lemma BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F1F2 : forall x : BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Type, (BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F1 x <= 7) /\ BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F2 (BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F1 x) = x. imp_solve. Qed.
Lemma BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F2F1 : forall (y : nat) (H : y <= 7), BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F1 (BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Record BeamFailureRecoveryConfig__ext0O__Type : Set :=
  make__BeamFailureRecoveryConfig__ext0O__Type {
    BeamFailureRecoveryConfig__ext0O__msg1_SubcarrierSpacing : option SubcarrierSpacing__Type ;
}.
Definition BeamFailureRecoveryConfig__ext0O__list := (
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 nil).
Definition BeamFailureRecoveryConfig__ext0O__cond z := 
  opt_cond SubcarrierSpacing__cond (BeamFailureRecoveryConfig__ext0O__msg1_SubcarrierSpacing z) /\
  True.

Definition BeamFailureRecoveryConfig__ext0__Type := BeamFailureRecoveryConfig__ext0O__Type.
Definition BeamFailureRecoveryConfig__ext0__cond := BeamFailureRecoveryConfig__ext0O__cond.

Require Import NR.RA_Prioritization.

Opaque RA_Prioritization__cond RA_Prioritization__Format.

Require Import NR.SetupRelease.
Require Import NR.CandidateBeamRSListExt_r16.
Definition BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__Type := SetupRelease__Type CandidateBeamRSListExt_r16__Type.
Definition BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__cond := SetupRelease__cond _ CandidateBeamRSListExt_r16__cond.
Definition BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__Format : T_Format BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__Type BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__cond := SetupRelease__Format _ _ CandidateBeamRSListExt_r16__Format.
Opaque BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__cond BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__Format.

Record BeamFailureRecoveryConfig__ext1O__Type : Set :=
  make__BeamFailureRecoveryConfig__ext1O__Type {
    BeamFailureRecoveryConfig__ext1O__ra_PrioritizationTwoStep_r16 : option RA_Prioritization__Type ;
    BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610 : option BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__Type ;
}.
Definition BeamFailureRecoveryConfig__ext1O__list := (
 Opt RA_Prioritization__Type RA_Prioritization__cond ::
 Opt BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__Type BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__cond ::
 nil).
Definition BeamFailureRecoveryConfig__ext1O__cond z := 
  opt_cond RA_Prioritization__cond (BeamFailureRecoveryConfig__ext1O__ra_PrioritizationTwoStep_r16 z) /\
  opt_cond BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__cond (BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610 z) /\
  True.

Definition BeamFailureRecoveryConfig__ext1__Type := BeamFailureRecoveryConfig__ext1O__Type.
Definition BeamFailureRecoveryConfig__ext1__cond := BeamFailureRecoveryConfig__ext1O__cond.

Inductive BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Type : Set :=
 | BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__true
.
Definition BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__cond := (fun (_ : BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Type) => True).
Lemma BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__nat__helper.

Definition BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F1 t :=
  match t with
  | BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__true => 0
  end.
Definition BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F2 n :=
  match n with
  | 0 => BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__true
  | _ => BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__true
  end.
Lemma BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F1F2 : forall x : BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Type, (BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F1 x <= 0) /\ BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F2 (BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F1 x) = x. imp_solve. Qed.
Lemma BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F2F1 : forall (y : nat) (H : y <= 0), BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F1 (BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F2 y) = y. enum_solve H y. Qed.

Record BeamFailureRecoveryConfig__ext2O__Type : Set :=
  make__BeamFailureRecoveryConfig__ext2O__Type {
    BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16 : option BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Type ;
}.
Definition BeamFailureRecoveryConfig__ext2O__list := (
 Opt BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Type BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__cond ::
 nil).
Definition BeamFailureRecoveryConfig__ext2O__cond z := 
  opt_cond BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__cond (BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16 z) /\
  True.

Definition BeamFailureRecoveryConfig__ext2__Type := BeamFailureRecoveryConfig__ext2O__Type.
Definition BeamFailureRecoveryConfig__ext2__cond := BeamFailureRecoveryConfig__ext2O__cond.

Record BeamFailureRecoveryConfig__Type : Set :=
  make__BeamFailureRecoveryConfig__Type {
    BeamFailureRecoveryConfig__rootSequenceIndex_BFR : option Z ;
    BeamFailureRecoveryConfig__rach_ConfigBFR : option RACH_ConfigGeneric__Type ;
    BeamFailureRecoveryConfig__rsrp_ThresholdSSB : option RSRP_Range__Type ;
    BeamFailureRecoveryConfig__candidateBeamRSList : option BeamFailureRecoveryConfig__candidateBeamRSList__Type ;
    BeamFailureRecoveryConfig__ssb_perRACH_Occasion : option BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Type ;
    BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex : option Z ;
    BeamFailureRecoveryConfig__recoverySearchSpaceId : option SearchSpaceId__Type ;
    BeamFailureRecoveryConfig__ra_Prioritization : option RA_Prioritization__Type ;
    BeamFailureRecoveryConfig__beamFailureRecoveryTimer : option BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Type ;
    BeamFailureRecoveryConfig__ext0 : option BeamFailureRecoveryConfig__ext0__Type ;
    BeamFailureRecoveryConfig__ext1 : option BeamFailureRecoveryConfig__ext1__Type ;
    BeamFailureRecoveryConfig__ext2 : option BeamFailureRecoveryConfig__ext2__Type ;
}.
Definition BeamFailureRecoveryConfig__root_list : list seq_elem := (
 Opt Z BeamFailureRecoveryConfig__rootSequenceIndex_BFR__cond ::
 Opt RACH_ConfigGeneric__Type RACH_ConfigGeneric__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt BeamFailureRecoveryConfig__candidateBeamRSList__Type BeamFailureRecoveryConfig__candidateBeamRSList__cond ::
 Opt BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Type BeamFailureRecoveryConfig__ssb_perRACH_Occasion__cond ::
 Opt Z BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__cond ::
 Opt SearchSpaceId__Type SearchSpaceId__cond ::
 Opt RA_Prioritization__Type RA_Prioritization__cond ::
 Opt BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Type BeamFailureRecoveryConfig__beamFailureRecoveryTimer__cond ::
 nil).
Definition BeamFailureRecoveryConfig__ext_list : list typ := (
  typ_cons BeamFailureRecoveryConfig__ext0__Type BeamFailureRecoveryConfig__ext0__cond ::
  typ_cons BeamFailureRecoveryConfig__ext1__Type BeamFailureRecoveryConfig__ext1__cond ::
  typ_cons BeamFailureRecoveryConfig__ext2__Type BeamFailureRecoveryConfig__ext2__cond ::
  nil).
Definition BeamFailureRecoveryConfig__cond (z : BeamFailureRecoveryConfig__Type) := 
(  opt_cond BeamFailureRecoveryConfig__rootSequenceIndex_BFR__cond (BeamFailureRecoveryConfig__rootSequenceIndex_BFR z) /\
  opt_cond RACH_ConfigGeneric__cond (BeamFailureRecoveryConfig__rach_ConfigBFR z) /\
  opt_cond RSRP_Range__cond (BeamFailureRecoveryConfig__rsrp_ThresholdSSB z) /\
  opt_cond BeamFailureRecoveryConfig__candidateBeamRSList__cond (BeamFailureRecoveryConfig__candidateBeamRSList z) /\
  opt_cond BeamFailureRecoveryConfig__ssb_perRACH_Occasion__cond (BeamFailureRecoveryConfig__ssb_perRACH_Occasion z) /\
  opt_cond BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__cond (BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex z) /\
  opt_cond SearchSpaceId__cond (BeamFailureRecoveryConfig__recoverySearchSpaceId z) /\
  opt_cond RA_Prioritization__cond (BeamFailureRecoveryConfig__ra_Prioritization z) /\
  opt_cond BeamFailureRecoveryConfig__beamFailureRecoveryTimer__cond (BeamFailureRecoveryConfig__beamFailureRecoveryTimer z) /\
  True) /\ 
(  opt_cond BeamFailureRecoveryConfig__ext0__cond (BeamFailureRecoveryConfig__ext0 z) /\
  opt_cond BeamFailureRecoveryConfig__ext1__cond (BeamFailureRecoveryConfig__ext1 z) /\
  opt_cond BeamFailureRecoveryConfig__ext2__cond (BeamFailureRecoveryConfig__ext2 z) /\
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
Definition BeamFailureRecoveryConfig__rootSequenceIndex_BFR__Format : T_Format Z BeamFailureRecoveryConfig__rootSequenceIndex_BFR__cond :=
 ranged_int_format (0) (137) BeamFailureRecoveryConfig__rootSequenceIndex_BFR__helper1 BeamFailureRecoveryConfig__rootSequenceIndex_BFR__helper2.

Opaque BeamFailureRecoveryConfig__rootSequenceIndex_BFR__cond BeamFailureRecoveryConfig__rootSequenceIndex_BFR__Format.

Definition BeamFailureRecoveryConfig__candidateBeamRSList__Format : T_Format BeamFailureRecoveryConfig__candidateBeamRSList__Type BeamFailureRecoveryConfig__candidateBeamRSList__cond := seq_of_format PRACH_ResourceDedicatedBFR__Format 1 maxNrofCandidateBeams BeamFailureRecoveryConfig__candidateBeamRSList__helper1 BeamFailureRecoveryConfig__candidateBeamRSList__helper2.

Opaque BeamFailureRecoveryConfig__candidateBeamRSList__cond BeamFailureRecoveryConfig__candidateBeamRSList__Format.

Definition BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Format : T_Format BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamFailureRecoveryConfig__ssb_perRACH_Occasion__nat__Format BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F1 BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F2 BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F1F2 BeamFailureRecoveryConfig__ssb_perRACH_Occasion__F2F1.

Opaque BeamFailureRecoveryConfig__ssb_perRACH_Occasion__cond BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Format.

Definition BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__Format : T_Format Z BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__cond :=
 ranged_int_format (0) (15) BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__helper1 BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__helper2.

Opaque BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__cond BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__Format.

Definition BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Format : T_Format BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamFailureRecoveryConfig__beamFailureRecoveryTimer__nat__Format BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F1 BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F2 BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F1F2 BeamFailureRecoveryConfig__beamFailureRecoveryTimer__F2F1.

Opaque BeamFailureRecoveryConfig__beamFailureRecoveryTimer__cond BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Format.


Definition BeamFailureRecoveryConfig__ext0O__Format_Type := Eval cbn in seq_format_prod BeamFailureRecoveryConfig__ext0O__list.
Definition BeamFailureRecoveryConfig__ext0O__Format_list : BeamFailureRecoveryConfig__ext0O__Format_Type :=
  (SubcarrierSpacing__Format, unit_format).
Definition BeamFailureRecoveryConfig__ext0O__list__Format := (*Eval compute in *) seq_format BeamFailureRecoveryConfig__ext0O__list BeamFailureRecoveryConfig__ext0O__Format_list.
Definition BeamFailureRecoveryConfig__ext0O__F1 z :=
  (BeamFailureRecoveryConfig__ext0O__msg1_SubcarrierSpacing z, tt).
Definition BeamFailureRecoveryConfig__ext0O__F2 (y : seq_type BeamFailureRecoveryConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__BeamFailureRecoveryConfig__ext0O__Type i0
  end.
Lemma BeamFailureRecoveryConfig__ext0O__F1F2_cond (z : BeamFailureRecoveryConfig__ext0O__Type)
  : BeamFailureRecoveryConfig__ext0O__cond z ->
  (seq_cond BeamFailureRecoveryConfig__ext0O__list (BeamFailureRecoveryConfig__ext0O__F1 z)).
intro H. unfold BeamFailureRecoveryConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma BeamFailureRecoveryConfig__ext0O__F1F2_cond2 (z : BeamFailureRecoveryConfig__ext0O__Type)
 : BeamFailureRecoveryConfig__ext0O__F2 (BeamFailureRecoveryConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BeamFailureRecoveryConfig__ext0O__F2F1_cond (y : seq_type BeamFailureRecoveryConfig__ext0O__list)
  : seq_cond BeamFailureRecoveryConfig__ext0O__list y ->
 (BeamFailureRecoveryConfig__ext0O__cond (BeamFailureRecoveryConfig__ext0O__F2 y)) /\  BeamFailureRecoveryConfig__ext0O__F1 (BeamFailureRecoveryConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BeamFailureRecoveryConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold BeamFailureRecoveryConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BeamFailureRecoveryConfig__ext0O__Format : T_Format BeamFailureRecoveryConfig__ext0O__Type BeamFailureRecoveryConfig__ext0O__cond :=
        proj2_format  BeamFailureRecoveryConfig__ext0O__cond BeamFailureRecoveryConfig__ext0O__list__Format
    BeamFailureRecoveryConfig__ext0O__F1 BeamFailureRecoveryConfig__ext0O__F2 BeamFailureRecoveryConfig__ext0O__F1F2_cond  BeamFailureRecoveryConfig__ext0O__F1F2_cond2 BeamFailureRecoveryConfig__ext0O__F2F1_cond.
Opaque BeamFailureRecoveryConfig__ext0O__cond BeamFailureRecoveryConfig__ext0O__Format.

Definition BeamFailureRecoveryConfig__ext0__check_all_none (b : BeamFailureRecoveryConfig__ext0O__Type) : bool :=
match b with 
  | make__BeamFailureRecoveryConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition BeamFailureRecoveryConfig__ext0__Format : T_Format BeamFailureRecoveryConfig__ext0__Type BeamFailureRecoveryConfig__ext0__cond :=
  restrict_add_format BeamFailureRecoveryConfig__ext0__check_all_none BeamFailureRecoveryConfig__ext0O__Format.

Opaque BeamFailureRecoveryConfig__ext0__cond BeamFailureRecoveryConfig__ext0__Format.

Opaque BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__cond BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__Format.


Definition BeamFailureRecoveryConfig__ext1O__Format_Type := Eval cbn in seq_format_prod BeamFailureRecoveryConfig__ext1O__list.
Definition BeamFailureRecoveryConfig__ext1O__Format_list : BeamFailureRecoveryConfig__ext1O__Format_Type :=
  (RA_Prioritization__Format, (BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610__Format, unit_format)).
Definition BeamFailureRecoveryConfig__ext1O__list__Format := (*Eval compute in *) seq_format BeamFailureRecoveryConfig__ext1O__list BeamFailureRecoveryConfig__ext1O__Format_list.
Definition BeamFailureRecoveryConfig__ext1O__F1 z :=
  (BeamFailureRecoveryConfig__ext1O__ra_PrioritizationTwoStep_r16 z, (BeamFailureRecoveryConfig__ext1O__candidateBeamRSListExt_v1610 z, tt)).
Definition BeamFailureRecoveryConfig__ext1O__F2 (y : seq_type BeamFailureRecoveryConfig__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BeamFailureRecoveryConfig__ext1O__Type i0 i1
  end.
Lemma BeamFailureRecoveryConfig__ext1O__F1F2_cond (z : BeamFailureRecoveryConfig__ext1O__Type)
  : BeamFailureRecoveryConfig__ext1O__cond z ->
  (seq_cond BeamFailureRecoveryConfig__ext1O__list (BeamFailureRecoveryConfig__ext1O__F1 z)).
intro H. unfold BeamFailureRecoveryConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma BeamFailureRecoveryConfig__ext1O__F1F2_cond2 (z : BeamFailureRecoveryConfig__ext1O__Type)
 : BeamFailureRecoveryConfig__ext1O__F2 (BeamFailureRecoveryConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BeamFailureRecoveryConfig__ext1O__F2F1_cond (y : seq_type BeamFailureRecoveryConfig__ext1O__list)
  : seq_cond BeamFailureRecoveryConfig__ext1O__list y ->
 (BeamFailureRecoveryConfig__ext1O__cond (BeamFailureRecoveryConfig__ext1O__F2 y)) /\  BeamFailureRecoveryConfig__ext1O__F1 (BeamFailureRecoveryConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BeamFailureRecoveryConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold BeamFailureRecoveryConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BeamFailureRecoveryConfig__ext1O__Format : T_Format BeamFailureRecoveryConfig__ext1O__Type BeamFailureRecoveryConfig__ext1O__cond :=
        proj2_format  BeamFailureRecoveryConfig__ext1O__cond BeamFailureRecoveryConfig__ext1O__list__Format
    BeamFailureRecoveryConfig__ext1O__F1 BeamFailureRecoveryConfig__ext1O__F2 BeamFailureRecoveryConfig__ext1O__F1F2_cond  BeamFailureRecoveryConfig__ext1O__F1F2_cond2 BeamFailureRecoveryConfig__ext1O__F2F1_cond.
Opaque BeamFailureRecoveryConfig__ext1O__cond BeamFailureRecoveryConfig__ext1O__Format.

Definition BeamFailureRecoveryConfig__ext1__check_all_none (b : BeamFailureRecoveryConfig__ext1O__Type) : bool :=
match b with 
  | make__BeamFailureRecoveryConfig__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition BeamFailureRecoveryConfig__ext1__Format : T_Format BeamFailureRecoveryConfig__ext1__Type BeamFailureRecoveryConfig__ext1__cond :=
  restrict_add_format BeamFailureRecoveryConfig__ext1__check_all_none BeamFailureRecoveryConfig__ext1O__Format.

Opaque BeamFailureRecoveryConfig__ext1__cond BeamFailureRecoveryConfig__ext1__Format.

Definition BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Format : T_Format BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__nat__Format BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F1 BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F2 BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F1F2 BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__F2F1.

Opaque BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__cond BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Format.


Definition BeamFailureRecoveryConfig__ext2O__Format_Type := Eval cbn in seq_format_prod BeamFailureRecoveryConfig__ext2O__list.
Definition BeamFailureRecoveryConfig__ext2O__Format_list : BeamFailureRecoveryConfig__ext2O__Format_Type :=
  (BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16__Format, unit_format).
Definition BeamFailureRecoveryConfig__ext2O__list__Format := (*Eval compute in *) seq_format BeamFailureRecoveryConfig__ext2O__list BeamFailureRecoveryConfig__ext2O__Format_list.
Definition BeamFailureRecoveryConfig__ext2O__F1 z :=
  (BeamFailureRecoveryConfig__ext2O__spCell_BFR_CBRA_r16 z, tt).
Definition BeamFailureRecoveryConfig__ext2O__F2 (y : seq_type BeamFailureRecoveryConfig__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__BeamFailureRecoveryConfig__ext2O__Type i0
  end.
Lemma BeamFailureRecoveryConfig__ext2O__F1F2_cond (z : BeamFailureRecoveryConfig__ext2O__Type)
  : BeamFailureRecoveryConfig__ext2O__cond z ->
  (seq_cond BeamFailureRecoveryConfig__ext2O__list (BeamFailureRecoveryConfig__ext2O__F1 z)).
intro H. unfold BeamFailureRecoveryConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma BeamFailureRecoveryConfig__ext2O__F1F2_cond2 (z : BeamFailureRecoveryConfig__ext2O__Type)
 : BeamFailureRecoveryConfig__ext2O__F2 (BeamFailureRecoveryConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BeamFailureRecoveryConfig__ext2O__F2F1_cond (y : seq_type BeamFailureRecoveryConfig__ext2O__list)
  : seq_cond BeamFailureRecoveryConfig__ext2O__list y ->
 (BeamFailureRecoveryConfig__ext2O__cond (BeamFailureRecoveryConfig__ext2O__F2 y)) /\  BeamFailureRecoveryConfig__ext2O__F1 (BeamFailureRecoveryConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BeamFailureRecoveryConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold BeamFailureRecoveryConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BeamFailureRecoveryConfig__ext2O__Format : T_Format BeamFailureRecoveryConfig__ext2O__Type BeamFailureRecoveryConfig__ext2O__cond :=
        proj2_format  BeamFailureRecoveryConfig__ext2O__cond BeamFailureRecoveryConfig__ext2O__list__Format
    BeamFailureRecoveryConfig__ext2O__F1 BeamFailureRecoveryConfig__ext2O__F2 BeamFailureRecoveryConfig__ext2O__F1F2_cond  BeamFailureRecoveryConfig__ext2O__F1F2_cond2 BeamFailureRecoveryConfig__ext2O__F2F1_cond.
Opaque BeamFailureRecoveryConfig__ext2O__cond BeamFailureRecoveryConfig__ext2O__Format.

Definition BeamFailureRecoveryConfig__ext2__check_all_none (b : BeamFailureRecoveryConfig__ext2O__Type) : bool :=
match b with 
  | make__BeamFailureRecoveryConfig__ext2O__Type None  => false 
  | _ => true 
 end.
Definition BeamFailureRecoveryConfig__ext2__Format : T_Format BeamFailureRecoveryConfig__ext2__Type BeamFailureRecoveryConfig__ext2__cond :=
  restrict_add_format BeamFailureRecoveryConfig__ext2__check_all_none BeamFailureRecoveryConfig__ext2O__Format.

Opaque BeamFailureRecoveryConfig__ext2__cond BeamFailureRecoveryConfig__ext2__Format.


Definition BeamFailureRecoveryConfig__root_Format_Type := Eval cbn in seq_format_prod BeamFailureRecoveryConfig__root_list.
Definition BeamFailureRecoveryConfig__root_Format_list : BeamFailureRecoveryConfig__root_Format_Type :=
  (BeamFailureRecoveryConfig__rootSequenceIndex_BFR__Format, (RACH_ConfigGeneric__Format, (RSRP_Range__Format, (BeamFailureRecoveryConfig__candidateBeamRSList__Format, (BeamFailureRecoveryConfig__ssb_perRACH_Occasion__Format, (BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex__Format, (SearchSpaceId__Format, (RA_Prioritization__Format, (BeamFailureRecoveryConfig__beamFailureRecoveryTimer__Format, unit_format))))))))).

Definition BeamFailureRecoveryConfig__ext_Format_Type := Eval cbn in get_formats BeamFailureRecoveryConfig__ext_list.
Definition BeamFailureRecoveryConfig__ext_Format_list : BeamFailureRecoveryConfig__ext_Format_Type :=
  (BeamFailureRecoveryConfig__ext0__Format, (BeamFailureRecoveryConfig__ext1__Format, (BeamFailureRecoveryConfig__ext2__Format, unit__Format))).

Definition BeamFailureRecoveryConfig__list_type : Set := (seq_type BeamFailureRecoveryConfig__root_list) * (seq_ext_type BeamFailureRecoveryConfig__ext_list).
Definition BeamFailureRecoveryConfig__list_cond (z : BeamFailureRecoveryConfig__list_type) : Prop :=
        (seq_cond BeamFailureRecoveryConfig__root_list (fst z)) /\ (seq_ext_cond BeamFailureRecoveryConfig__ext_list (snd z)).
Definition BeamFailureRecoveryConfig__list_format : T_Format BeamFailureRecoveryConfig__list_type BeamFailureRecoveryConfig__list_cond :=
 (* Eval compute in *) seq_ext_format BeamFailureRecoveryConfig__root_list BeamFailureRecoveryConfig__root_Format_list BeamFailureRecoveryConfig__ext_list BeamFailureRecoveryConfig__ext_Format_list.

Opaque BeamFailureRecoveryConfig__list_format.
Definition BeamFailureRecoveryConfig__F1 (z : BeamFailureRecoveryConfig__Type) : BeamFailureRecoveryConfig__list_type :=
  (((BeamFailureRecoveryConfig__rootSequenceIndex_BFR z, (BeamFailureRecoveryConfig__rach_ConfigBFR z, (BeamFailureRecoveryConfig__rsrp_ThresholdSSB z, (BeamFailureRecoveryConfig__candidateBeamRSList z, (BeamFailureRecoveryConfig__ssb_perRACH_Occasion z, (BeamFailureRecoveryConfig__ra_ssb_OccasionMaskIndex z, (BeamFailureRecoveryConfig__recoverySearchSpaceId z, (BeamFailureRecoveryConfig__ra_Prioritization z, (BeamFailureRecoveryConfig__beamFailureRecoveryTimer z, tt)))))))))), (
(BeamFailureRecoveryConfig__ext0 z, (BeamFailureRecoveryConfig__ext1 z, (BeamFailureRecoveryConfig__ext2 z, tt))))).
Definition BeamFailureRecoveryConfig__F2 (y : BeamFailureRecoveryConfig__list_type) : BeamFailureRecoveryConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), (i0, (i1, (i2, _))))=>
    make__BeamFailureRecoveryConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 i0 i1 i2
  end.
Definition BeamFailureRecoveryConfig__helper1 : (forall a : BeamFailureRecoveryConfig__Type, BeamFailureRecoveryConfig__cond a -> BeamFailureRecoveryConfig__list_cond (BeamFailureRecoveryConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BeamFailureRecoveryConfig__helper2 : (forall a : BeamFailureRecoveryConfig__Type, BeamFailureRecoveryConfig__F2 (BeamFailureRecoveryConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BeamFailureRecoveryConfig__helper3 : (forall b : BeamFailureRecoveryConfig__list_type, BeamFailureRecoveryConfig__list_cond b -> BeamFailureRecoveryConfig__cond (BeamFailureRecoveryConfig__F2 b) /\ BeamFailureRecoveryConfig__F1 (BeamFailureRecoveryConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BeamFailureRecoveryConfig__cond, BeamFailureRecoveryConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BeamFailureRecoveryConfig__Format : T_Format BeamFailureRecoveryConfig__Type BeamFailureRecoveryConfig__cond :=
 proj2_format BeamFailureRecoveryConfig__cond BeamFailureRecoveryConfig__list_format  BeamFailureRecoveryConfig__F1 BeamFailureRecoveryConfig__F2 BeamFailureRecoveryConfig__helper1 BeamFailureRecoveryConfig__helper2 BeamFailureRecoveryConfig__helper3.

Opaque BeamFailureRecoveryConfig__cond BeamFailureRecoveryConfig__Format.

