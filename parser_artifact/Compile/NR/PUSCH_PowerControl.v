Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PUSCH_PowerControl__tpc_Accumulation__Type : Set :=
 | PUSCH_PowerControl__tpc_Accumulation__disabled
.
Definition PUSCH_PowerControl__tpc_Accumulation__cond := (fun (_ : PUSCH_PowerControl__tpc_Accumulation__Type) => True).
Lemma PUSCH_PowerControl__tpc_Accumulation__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_PowerControl__tpc_Accumulation__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_PowerControl__tpc_Accumulation__nat__helper.

Definition PUSCH_PowerControl__tpc_Accumulation__F1 t :=
  match t with
  | PUSCH_PowerControl__tpc_Accumulation__disabled => 0
  end.
Definition PUSCH_PowerControl__tpc_Accumulation__F2 n :=
  match n with
  | 0 => PUSCH_PowerControl__tpc_Accumulation__disabled
  | _ => PUSCH_PowerControl__tpc_Accumulation__disabled
  end.
Lemma PUSCH_PowerControl__tpc_Accumulation__F1F2 : forall x : PUSCH_PowerControl__tpc_Accumulation__Type, (PUSCH_PowerControl__tpc_Accumulation__F1 x <= 0) /\ PUSCH_PowerControl__tpc_Accumulation__F2 (PUSCH_PowerControl__tpc_Accumulation__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_PowerControl__tpc_Accumulation__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_PowerControl__tpc_Accumulation__F1 (PUSCH_PowerControl__tpc_Accumulation__F2 y) = y. enum_solve H y. Qed.

Require Import NR.Alpha.

Opaque Alpha__cond Alpha__Format.

Lemma PUSCH_PowerControl__p0_NominalWithoutGrant__helper1 : (-202 <= 24)%Z.  lia. Qed.
Lemma PUSCH_PowerControl__p0_NominalWithoutGrant__helper2 : to_bit_sz (Z.to_nat (24 - -202)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (24 - -202))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl__p0_NominalWithoutGrant__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl__p0_NominalWithoutGrant__Type := Z.
Definition PUSCH_PowerControl__p0_NominalWithoutGrant__cond := (fun z => (-202 <= z <= 24)%Z).
Require Import NR.P0_PUSCH_AlphaSet.

Opaque P0_PUSCH_AlphaSet__cond P0_PUSCH_AlphaSet__Format.

Definition PUSCH_PowerControl__p0_AlphaSets__Type := list P0_PUSCH_AlphaSet__Type.

Lemma PUSCH_PowerControl__p0_AlphaSets__helper1 : (0 <= 1 <= maxNrofP0_PUSCH_AlphaSets)%Z. unfold maxNrofP0_PUSCH_AlphaSets.
 lia. Qed.
Lemma PUSCH_PowerControl__p0_AlphaSets__helper2 : to_bit_sz (Z.to_nat (maxNrofP0_PUSCH_AlphaSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofP0_PUSCH_AlphaSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl__p0_AlphaSets__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl__p0_AlphaSets__cond (z : PUSCH_PowerControl__p0_AlphaSets__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofP0_PUSCH_AlphaSets)%Z /\ (list_and P0_PUSCH_AlphaSet__cond z) .

Require Import NR.PUSCH_PathlossReferenceRS.

Opaque PUSCH_PathlossReferenceRS__cond PUSCH_PathlossReferenceRS__Format.

Definition PUSCH_PowerControl__pathlossReferenceRSToAddModList__Type := list PUSCH_PathlossReferenceRS__Type.

Lemma PUSCH_PowerControl__pathlossReferenceRSToAddModList__helper1 : (0 <= 1 <= maxNrofPUSCH_PathlossReferenceRSs)%Z. unfold maxNrofPUSCH_PathlossReferenceRSs.
 lia. Qed.
Lemma PUSCH_PowerControl__pathlossReferenceRSToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofPUSCH_PathlossReferenceRSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUSCH_PathlossReferenceRSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl__pathlossReferenceRSToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl__pathlossReferenceRSToAddModList__cond (z : PUSCH_PowerControl__pathlossReferenceRSToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUSCH_PathlossReferenceRSs)%Z /\ (list_and PUSCH_PathlossReferenceRS__cond z) .

Require Import NR.PUSCH_PathlossReferenceRS_Id.

Opaque PUSCH_PathlossReferenceRS_Id__cond PUSCH_PathlossReferenceRS_Id__Format.

Definition PUSCH_PowerControl__pathlossReferenceRSToReleaseList__Type := list PUSCH_PathlossReferenceRS_Id__Type.

Lemma PUSCH_PowerControl__pathlossReferenceRSToReleaseList__helper1 : (0 <= 1 <= maxNrofPUSCH_PathlossReferenceRSs)%Z. unfold maxNrofPUSCH_PathlossReferenceRSs.
 lia. Qed.
Lemma PUSCH_PowerControl__pathlossReferenceRSToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofPUSCH_PathlossReferenceRSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUSCH_PathlossReferenceRSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl__pathlossReferenceRSToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl__pathlossReferenceRSToReleaseList__cond (z : PUSCH_PowerControl__pathlossReferenceRSToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUSCH_PathlossReferenceRSs)%Z /\ (list_and PUSCH_PathlossReferenceRS_Id__cond z) .

Inductive PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Type : Set :=
 | PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__twoStates
.
Definition PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__cond := (fun (_ : PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Type) => True).
Lemma PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__nat__helper.

Definition PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F1 t :=
  match t with
  | PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__twoStates => 0
  end.
Definition PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F2 n :=
  match n with
  | 0 => PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__twoStates
  | _ => PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__twoStates
  end.
Lemma PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F1F2 : forall x : PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Type, (PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F1 x <= 0) /\ PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F2 (PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F1 (PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_PowerControl__deltaMCS__Type : Set :=
 | PUSCH_PowerControl__deltaMCS__enabled
.
Definition PUSCH_PowerControl__deltaMCS__cond := (fun (_ : PUSCH_PowerControl__deltaMCS__Type) => True).
Lemma PUSCH_PowerControl__deltaMCS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_PowerControl__deltaMCS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_PowerControl__deltaMCS__nat__helper.

Definition PUSCH_PowerControl__deltaMCS__F1 t :=
  match t with
  | PUSCH_PowerControl__deltaMCS__enabled => 0
  end.
Definition PUSCH_PowerControl__deltaMCS__F2 n :=
  match n with
  | 0 => PUSCH_PowerControl__deltaMCS__enabled
  | _ => PUSCH_PowerControl__deltaMCS__enabled
  end.
Lemma PUSCH_PowerControl__deltaMCS__F1F2 : forall x : PUSCH_PowerControl__deltaMCS__Type, (PUSCH_PowerControl__deltaMCS__F1 x <= 0) /\ PUSCH_PowerControl__deltaMCS__F2 (PUSCH_PowerControl__deltaMCS__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_PowerControl__deltaMCS__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_PowerControl__deltaMCS__F1 (PUSCH_PowerControl__deltaMCS__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SRI_PUSCH_PowerControl.

Opaque SRI_PUSCH_PowerControl__cond SRI_PUSCH_PowerControl__Format.

Definition PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__Type := list SRI_PUSCH_PowerControl__Type.

Lemma PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__helper1 : (0 <= 1 <= maxNrofSRI_PUSCH_Mappings)%Z. unfold maxNrofSRI_PUSCH_Mappings.
 lia. Qed.
Lemma PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofSRI_PUSCH_Mappings - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRI_PUSCH_Mappings - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__cond (z : PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRI_PUSCH_Mappings)%Z /\ (list_and SRI_PUSCH_PowerControl__cond z) .

Require Import NR.SRI_PUSCH_PowerControlId.

Opaque SRI_PUSCH_PowerControlId__cond SRI_PUSCH_PowerControlId__Format.

Definition PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__Type := list SRI_PUSCH_PowerControlId__Type.

Lemma PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__helper1 : (0 <= 1 <= maxNrofSRI_PUSCH_Mappings)%Z. unfold maxNrofSRI_PUSCH_Mappings.
 lia. Qed.
Lemma PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofSRI_PUSCH_Mappings - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRI_PUSCH_Mappings - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__cond (z : PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRI_PUSCH_Mappings)%Z /\ (list_and SRI_PUSCH_PowerControlId__cond z) .

Record PUSCH_PowerControl__Type : Set :=
  make__PUSCH_PowerControl__Type {
    PUSCH_PowerControl__tpc_Accumulation : option PUSCH_PowerControl__tpc_Accumulation__Type ;
    PUSCH_PowerControl__msg3_Alpha : option Alpha__Type ;
    PUSCH_PowerControl__p0_NominalWithoutGrant : option Z ;
    PUSCH_PowerControl__p0_AlphaSets : option PUSCH_PowerControl__p0_AlphaSets__Type ;
    PUSCH_PowerControl__pathlossReferenceRSToAddModList : option PUSCH_PowerControl__pathlossReferenceRSToAddModList__Type ;
    PUSCH_PowerControl__pathlossReferenceRSToReleaseList : option PUSCH_PowerControl__pathlossReferenceRSToReleaseList__Type ;
    PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates : option PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Type ;
    PUSCH_PowerControl__deltaMCS : option PUSCH_PowerControl__deltaMCS__Type ;
    PUSCH_PowerControl__sri_PUSCH_MappingToAddModList : option PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__Type ;
    PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList : option PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__Type ;
}.
Definition PUSCH_PowerControl__list := (
 Opt PUSCH_PowerControl__tpc_Accumulation__Type PUSCH_PowerControl__tpc_Accumulation__cond ::
 Opt Alpha__Type Alpha__cond ::
 Opt Z PUSCH_PowerControl__p0_NominalWithoutGrant__cond ::
 Opt PUSCH_PowerControl__p0_AlphaSets__Type PUSCH_PowerControl__p0_AlphaSets__cond ::
 Opt PUSCH_PowerControl__pathlossReferenceRSToAddModList__Type PUSCH_PowerControl__pathlossReferenceRSToAddModList__cond ::
 Opt PUSCH_PowerControl__pathlossReferenceRSToReleaseList__Type PUSCH_PowerControl__pathlossReferenceRSToReleaseList__cond ::
 Opt PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Type PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__cond ::
 Opt PUSCH_PowerControl__deltaMCS__Type PUSCH_PowerControl__deltaMCS__cond ::
 Opt PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__Type PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__cond ::
 Opt PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__Type PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__cond ::
 nil).
Definition PUSCH_PowerControl__cond z := 
  opt_cond PUSCH_PowerControl__tpc_Accumulation__cond (PUSCH_PowerControl__tpc_Accumulation z) /\
  opt_cond Alpha__cond (PUSCH_PowerControl__msg3_Alpha z) /\
  opt_cond PUSCH_PowerControl__p0_NominalWithoutGrant__cond (PUSCH_PowerControl__p0_NominalWithoutGrant z) /\
  opt_cond PUSCH_PowerControl__p0_AlphaSets__cond (PUSCH_PowerControl__p0_AlphaSets z) /\
  opt_cond PUSCH_PowerControl__pathlossReferenceRSToAddModList__cond (PUSCH_PowerControl__pathlossReferenceRSToAddModList z) /\
  opt_cond PUSCH_PowerControl__pathlossReferenceRSToReleaseList__cond (PUSCH_PowerControl__pathlossReferenceRSToReleaseList z) /\
  opt_cond PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__cond (PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates z) /\
  opt_cond PUSCH_PowerControl__deltaMCS__cond (PUSCH_PowerControl__deltaMCS z) /\
  opt_cond PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__cond (PUSCH_PowerControl__sri_PUSCH_MappingToAddModList z) /\
  opt_cond PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__cond (PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList z) /\
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
Definition PUSCH_PowerControl__tpc_Accumulation__Format : T_Format PUSCH_PowerControl__tpc_Accumulation__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_PowerControl__tpc_Accumulation__nat__Format PUSCH_PowerControl__tpc_Accumulation__F1 PUSCH_PowerControl__tpc_Accumulation__F2 PUSCH_PowerControl__tpc_Accumulation__F1F2 PUSCH_PowerControl__tpc_Accumulation__F2F1.

Opaque PUSCH_PowerControl__tpc_Accumulation__cond PUSCH_PowerControl__tpc_Accumulation__Format.

Definition PUSCH_PowerControl__p0_NominalWithoutGrant__Format : T_Format Z PUSCH_PowerControl__p0_NominalWithoutGrant__cond :=
 ranged_int_format (-202) (24) PUSCH_PowerControl__p0_NominalWithoutGrant__helper1 PUSCH_PowerControl__p0_NominalWithoutGrant__helper2.

Opaque PUSCH_PowerControl__p0_NominalWithoutGrant__cond PUSCH_PowerControl__p0_NominalWithoutGrant__Format.

Definition PUSCH_PowerControl__p0_AlphaSets__Format : T_Format PUSCH_PowerControl__p0_AlphaSets__Type PUSCH_PowerControl__p0_AlphaSets__cond := seq_of_format P0_PUSCH_AlphaSet__Format 1 maxNrofP0_PUSCH_AlphaSets PUSCH_PowerControl__p0_AlphaSets__helper1 PUSCH_PowerControl__p0_AlphaSets__helper2.

Opaque PUSCH_PowerControl__p0_AlphaSets__cond PUSCH_PowerControl__p0_AlphaSets__Format.

Definition PUSCH_PowerControl__pathlossReferenceRSToAddModList__Format : T_Format PUSCH_PowerControl__pathlossReferenceRSToAddModList__Type PUSCH_PowerControl__pathlossReferenceRSToAddModList__cond := seq_of_format PUSCH_PathlossReferenceRS__Format 1 maxNrofPUSCH_PathlossReferenceRSs PUSCH_PowerControl__pathlossReferenceRSToAddModList__helper1 PUSCH_PowerControl__pathlossReferenceRSToAddModList__helper2.

Opaque PUSCH_PowerControl__pathlossReferenceRSToAddModList__cond PUSCH_PowerControl__pathlossReferenceRSToAddModList__Format.

Definition PUSCH_PowerControl__pathlossReferenceRSToReleaseList__Format : T_Format PUSCH_PowerControl__pathlossReferenceRSToReleaseList__Type PUSCH_PowerControl__pathlossReferenceRSToReleaseList__cond := seq_of_format PUSCH_PathlossReferenceRS_Id__Format 1 maxNrofPUSCH_PathlossReferenceRSs PUSCH_PowerControl__pathlossReferenceRSToReleaseList__helper1 PUSCH_PowerControl__pathlossReferenceRSToReleaseList__helper2.

Opaque PUSCH_PowerControl__pathlossReferenceRSToReleaseList__cond PUSCH_PowerControl__pathlossReferenceRSToReleaseList__Format.

Definition PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Format : T_Format PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__nat__Format PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F1 PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F2 PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F1F2 PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__F2F1.

Opaque PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__cond PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Format.

Definition PUSCH_PowerControl__deltaMCS__Format : T_Format PUSCH_PowerControl__deltaMCS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_PowerControl__deltaMCS__nat__Format PUSCH_PowerControl__deltaMCS__F1 PUSCH_PowerControl__deltaMCS__F2 PUSCH_PowerControl__deltaMCS__F1F2 PUSCH_PowerControl__deltaMCS__F2F1.

Opaque PUSCH_PowerControl__deltaMCS__cond PUSCH_PowerControl__deltaMCS__Format.

Definition PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__Format : T_Format PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__Type PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__cond := seq_of_format SRI_PUSCH_PowerControl__Format 1 maxNrofSRI_PUSCH_Mappings PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__helper1 PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__helper2.

Opaque PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__cond PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__Format.

Definition PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__Format : T_Format PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__Type PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__cond := seq_of_format SRI_PUSCH_PowerControlId__Format 1 maxNrofSRI_PUSCH_Mappings PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__helper1 PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__helper2.

Opaque PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__cond PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__Format.


Definition PUSCH_PowerControl__Format_Type := Eval cbn in seq_format_prod PUSCH_PowerControl__list.
Definition PUSCH_PowerControl__Format_list : PUSCH_PowerControl__Format_Type :=
  (PUSCH_PowerControl__tpc_Accumulation__Format, (Alpha__Format, (PUSCH_PowerControl__p0_NominalWithoutGrant__Format, (PUSCH_PowerControl__p0_AlphaSets__Format, (PUSCH_PowerControl__pathlossReferenceRSToAddModList__Format, (PUSCH_PowerControl__pathlossReferenceRSToReleaseList__Format, (PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates__Format, (PUSCH_PowerControl__deltaMCS__Format, (PUSCH_PowerControl__sri_PUSCH_MappingToAddModList__Format, (PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList__Format, unit_format)))))))))).
Definition PUSCH_PowerControl__list__Format := (*Eval compute in *) seq_format PUSCH_PowerControl__list PUSCH_PowerControl__Format_list.
Definition PUSCH_PowerControl__F1 z :=
  (PUSCH_PowerControl__tpc_Accumulation z, (PUSCH_PowerControl__msg3_Alpha z, (PUSCH_PowerControl__p0_NominalWithoutGrant z, (PUSCH_PowerControl__p0_AlphaSets z, (PUSCH_PowerControl__pathlossReferenceRSToAddModList z, (PUSCH_PowerControl__pathlossReferenceRSToReleaseList z, (PUSCH_PowerControl__twoPUSCH_PC_AdjustmentStates z, (PUSCH_PowerControl__deltaMCS z, (PUSCH_PowerControl__sri_PUSCH_MappingToAddModList z, (PUSCH_PowerControl__sri_PUSCH_MappingToReleaseList z, tt)))))))))).
Definition PUSCH_PowerControl__F2 (y : seq_type PUSCH_PowerControl__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__PUSCH_PowerControl__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma PUSCH_PowerControl__F1F2_cond (z : PUSCH_PowerControl__Type)
  : PUSCH_PowerControl__cond z ->
  (seq_cond PUSCH_PowerControl__list (PUSCH_PowerControl__F1 z)).
intro H. unfold PUSCH_PowerControl__cond in H. simpl. auto. Qed.
Lemma PUSCH_PowerControl__F1F2_cond2 (z : PUSCH_PowerControl__Type)
 : PUSCH_PowerControl__F2 (PUSCH_PowerControl__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_PowerControl__F2F1_cond (y : seq_type PUSCH_PowerControl__list)
  : seq_cond PUSCH_PowerControl__list y ->
 (PUSCH_PowerControl__cond (PUSCH_PowerControl__F2 y)) /\  PUSCH_PowerControl__F1 (PUSCH_PowerControl__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_PowerControl__cond. simpl in *. auto.
 - simpl. unfold PUSCH_PowerControl__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_PowerControl__Format : T_Format PUSCH_PowerControl__Type PUSCH_PowerControl__cond :=
        proj2_format  PUSCH_PowerControl__cond PUSCH_PowerControl__list__Format
    PUSCH_PowerControl__F1 PUSCH_PowerControl__F2 PUSCH_PowerControl__F1F2_cond  PUSCH_PowerControl__F1F2_cond2 PUSCH_PowerControl__F2F1_cond.
Opaque PUSCH_PowerControl__cond PUSCH_PowerControl__Format.

