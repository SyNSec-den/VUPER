Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandCombination.

Opaque BandCombination__cond BandCombination__Format.

Require Import NR.BandCombination_v1540.

Opaque BandCombination_v1540__cond BandCombination_v1540__Format.

Require Import NR.BandCombination_v1560.

Opaque BandCombination_v1560__cond BandCombination_v1560__Format.

Require Import NR.BandCombination_v1570.

Opaque BandCombination_v1570__cond BandCombination_v1570__Format.

Require Import NR.BandCombination_v1580.

Opaque BandCombination_v1580__cond BandCombination_v1580__Format.

Require Import NR.BandCombination_v1590.

Opaque BandCombination_v1590__cond BandCombination_v1590__Format.

Require Import NR.BandCombination_v1610.

Opaque BandCombination_v1610__cond BandCombination_v1610__Format.

Require Import NR.ULTxSwitchingBandPair_r16.

Opaque ULTxSwitchingBandPair_r16__cond ULTxSwitchingBandPair_r16__Format.

Definition BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__Type := list ULTxSwitchingBandPair_r16__Type.

Lemma BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__helper1 : (0 <= 1 <= maxULTxSwitchingBandPairs)%Z. unfold maxULTxSwitchingBandPairs.
 lia. Qed.
Lemma BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__helper2 : to_bit_sz (Z.to_nat (maxULTxSwitchingBandPairs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxULTxSwitchingBandPairs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__cond (z : BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxULTxSwitchingBandPairs)%Z /\ (list_and ULTxSwitchingBandPair_r16__cond z) .

Inductive BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Type : Set :=
 | BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__switchedUL
 | BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__dualUL
 | BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__both
.
Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__cond := (fun (_ : BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Type) => True).
Lemma BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__nat__helper.

Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F1 t :=
  match t with
  | BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__switchedUL => 0
  | BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__dualUL => 1
  | BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__both => 2
  end.
Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F2 n :=
  match n with
  | 0 => BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__switchedUL
  | 1 => BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__dualUL
  | 2 => BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__both
  | _ => BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__switchedUL
  end.
Lemma BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F1F2 : forall x : BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Type, (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F1 x <= 2) /\ BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F2 (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F1 x) = x. imp_solve. Qed.
Lemma BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F2F1 : forall (y : nat) (H : y <= 2), BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F1 (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Type : Set :=
 | BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__supported
.
Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__cond := (fun (_ : BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Type) => True).
Lemma BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__nat__helper.

Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F1 t :=
  match t with
  | BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__supported => 0
  end.
Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F2 n :=
  match n with
  | 0 => BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__supported
  | _ => BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__supported
  end.
Lemma BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F1F2 : forall x : BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Type, (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F1 x <= 0) /\ BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F2 (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F1 x) = x. imp_solve. Qed.
Lemma BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F2F1 : forall (y : nat) (H : y <= 0), BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F1 (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Type : Set :=
 | BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__nonCoherent
 | BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__fullCoherent
.
Definition BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__cond := (fun (_ : BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Type) => True).
Lemma BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__nat__helper.

Definition BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F1 t :=
  match t with
  | BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__nonCoherent => 0
  | BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__fullCoherent => 1
  end.
Definition BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F2 n :=
  match n with
  | 0 => BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__nonCoherent
  | 1 => BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__fullCoherent
  | _ => BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__nonCoherent
  end.
Lemma BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F1F2 : forall x : BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Type, (BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F1 x <= 1) /\ BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F2 (BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F1 x) = x. imp_solve. Qed.
Lemma BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F2F1 : forall (y : nat) (H : y <= 1), BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F1 (BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F2 y) = y. enum_solve H y. Qed.

Record BandCombination_UplinkTxSwitch_r16__ext0O__Type : Set :=
  make__BandCombination_UplinkTxSwitch_r16__ext0O__Type {
    BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16 : option BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Type ;
}.
Definition BandCombination_UplinkTxSwitch_r16__ext0O__list := (
 Opt BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Type BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__cond ::
 nil).
Definition BandCombination_UplinkTxSwitch_r16__ext0O__cond z := 
  opt_cond BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__cond (BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16 z) /\
  True.

Definition BandCombination_UplinkTxSwitch_r16__ext0__Type := BandCombination_UplinkTxSwitch_r16__ext0O__Type.
Definition BandCombination_UplinkTxSwitch_r16__ext0__cond := BandCombination_UplinkTxSwitch_r16__ext0O__cond.

Record BandCombination_UplinkTxSwitch_r16__Type : Set :=
  make__BandCombination_UplinkTxSwitch_r16__Type {
    BandCombination_UplinkTxSwitch_r16__bandCombination_r16 : BandCombination__Type ;
    BandCombination_UplinkTxSwitch_r16__bandCombination_v1540 : option BandCombination_v1540__Type ;
    BandCombination_UplinkTxSwitch_r16__bandCombination_v1560 : option BandCombination_v1560__Type ;
    BandCombination_UplinkTxSwitch_r16__bandCombination_v1570 : option BandCombination_v1570__Type ;
    BandCombination_UplinkTxSwitch_r16__bandCombination_v1580 : option BandCombination_v1580__Type ;
    BandCombination_UplinkTxSwitch_r16__bandCombination_v1590 : option BandCombination_v1590__Type ;
    BandCombination_UplinkTxSwitch_r16__bandCombination_v1610 : option BandCombination_v1610__Type ;
    BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16 : BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__Type ;
    BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16 : option BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Type ;
    BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16 : option BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Type ;
    BandCombination_UplinkTxSwitch_r16__ext0 : option BandCombination_UplinkTxSwitch_r16__ext0__Type ;
}.
Definition BandCombination_UplinkTxSwitch_r16__root_list : list seq_elem := (
 Nor BandCombination__Type BandCombination__cond ::
 Opt BandCombination_v1540__Type BandCombination_v1540__cond ::
 Opt BandCombination_v1560__Type BandCombination_v1560__cond ::
 Opt BandCombination_v1570__Type BandCombination_v1570__cond ::
 Opt BandCombination_v1580__Type BandCombination_v1580__cond ::
 Opt BandCombination_v1590__Type BandCombination_v1590__cond ::
 Opt BandCombination_v1610__Type BandCombination_v1610__cond ::
 Nor BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__Type BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__cond ::
 Opt BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Type BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__cond ::
 Opt BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Type BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__cond ::
 nil).
Definition BandCombination_UplinkTxSwitch_r16__ext_list : list typ := (
  typ_cons BandCombination_UplinkTxSwitch_r16__ext0__Type BandCombination_UplinkTxSwitch_r16__ext0__cond ::
  nil).
Definition BandCombination_UplinkTxSwitch_r16__cond (z : BandCombination_UplinkTxSwitch_r16__Type) := 
(  BandCombination__cond (BandCombination_UplinkTxSwitch_r16__bandCombination_r16 z) /\
  opt_cond BandCombination_v1540__cond (BandCombination_UplinkTxSwitch_r16__bandCombination_v1540 z) /\
  opt_cond BandCombination_v1560__cond (BandCombination_UplinkTxSwitch_r16__bandCombination_v1560 z) /\
  opt_cond BandCombination_v1570__cond (BandCombination_UplinkTxSwitch_r16__bandCombination_v1570 z) /\
  opt_cond BandCombination_v1580__cond (BandCombination_UplinkTxSwitch_r16__bandCombination_v1580 z) /\
  opt_cond BandCombination_v1590__cond (BandCombination_UplinkTxSwitch_r16__bandCombination_v1590 z) /\
  opt_cond BandCombination_v1610__cond (BandCombination_UplinkTxSwitch_r16__bandCombination_v1610 z) /\
  BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__cond (BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16 z) /\
  opt_cond BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__cond (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16 z) /\
  opt_cond BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__cond (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16 z) /\
  True) /\ 
(  opt_cond BandCombination_UplinkTxSwitch_r16__ext0__cond (BandCombination_UplinkTxSwitch_r16__ext0 z) /\
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
Definition BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__Format : T_Format BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__Type BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__cond := seq_of_format ULTxSwitchingBandPair_r16__Format 1 maxULTxSwitchingBandPairs BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__helper1 BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__helper2.

Opaque BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__cond BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__Format.

Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Format : T_Format BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__nat__Format BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F1 BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F2 BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F1F2 BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__F2F1.

Opaque BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__cond BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Format.

Definition BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Format : T_Format BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__nat__Format BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F1 BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F2 BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F1F2 BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__F2F1.

Opaque BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__cond BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Format.

Definition BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Format : T_Format BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__nat__Format BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F1 BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F2 BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F1F2 BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__F2F1.

Opaque BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__cond BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Format.


Definition BandCombination_UplinkTxSwitch_r16__ext0O__Format_Type := Eval cbn in seq_format_prod BandCombination_UplinkTxSwitch_r16__ext0O__list.
Definition BandCombination_UplinkTxSwitch_r16__ext0O__Format_list : BandCombination_UplinkTxSwitch_r16__ext0O__Format_Type :=
  (BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16__Format, unit_format).
Definition BandCombination_UplinkTxSwitch_r16__ext0O__list__Format := (*Eval compute in *) seq_format BandCombination_UplinkTxSwitch_r16__ext0O__list BandCombination_UplinkTxSwitch_r16__ext0O__Format_list.
Definition BandCombination_UplinkTxSwitch_r16__ext0O__F1 z :=
  (BandCombination_UplinkTxSwitch_r16__ext0O__uplinkTxSwitching_PUSCH_TransCoherence_r16 z, tt).
Definition BandCombination_UplinkTxSwitch_r16__ext0O__F2 (y : seq_type BandCombination_UplinkTxSwitch_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__BandCombination_UplinkTxSwitch_r16__ext0O__Type i0
  end.
Lemma BandCombination_UplinkTxSwitch_r16__ext0O__F1F2_cond (z : BandCombination_UplinkTxSwitch_r16__ext0O__Type)
  : BandCombination_UplinkTxSwitch_r16__ext0O__cond z ->
  (seq_cond BandCombination_UplinkTxSwitch_r16__ext0O__list (BandCombination_UplinkTxSwitch_r16__ext0O__F1 z)).
intro H. unfold BandCombination_UplinkTxSwitch_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma BandCombination_UplinkTxSwitch_r16__ext0O__F1F2_cond2 (z : BandCombination_UplinkTxSwitch_r16__ext0O__Type)
 : BandCombination_UplinkTxSwitch_r16__ext0O__F2 (BandCombination_UplinkTxSwitch_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombination_UplinkTxSwitch_r16__ext0O__F2F1_cond (y : seq_type BandCombination_UplinkTxSwitch_r16__ext0O__list)
  : seq_cond BandCombination_UplinkTxSwitch_r16__ext0O__list y ->
 (BandCombination_UplinkTxSwitch_r16__ext0O__cond (BandCombination_UplinkTxSwitch_r16__ext0O__F2 y)) /\  BandCombination_UplinkTxSwitch_r16__ext0O__F1 (BandCombination_UplinkTxSwitch_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombination_UplinkTxSwitch_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold BandCombination_UplinkTxSwitch_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombination_UplinkTxSwitch_r16__ext0O__Format : T_Format BandCombination_UplinkTxSwitch_r16__ext0O__Type BandCombination_UplinkTxSwitch_r16__ext0O__cond :=
        proj2_format  BandCombination_UplinkTxSwitch_r16__ext0O__cond BandCombination_UplinkTxSwitch_r16__ext0O__list__Format
    BandCombination_UplinkTxSwitch_r16__ext0O__F1 BandCombination_UplinkTxSwitch_r16__ext0O__F2 BandCombination_UplinkTxSwitch_r16__ext0O__F1F2_cond  BandCombination_UplinkTxSwitch_r16__ext0O__F1F2_cond2 BandCombination_UplinkTxSwitch_r16__ext0O__F2F1_cond.
Opaque BandCombination_UplinkTxSwitch_r16__ext0O__cond BandCombination_UplinkTxSwitch_r16__ext0O__Format.

Definition BandCombination_UplinkTxSwitch_r16__ext0__check_all_none (b : BandCombination_UplinkTxSwitch_r16__ext0O__Type) : bool :=
match b with 
  | make__BandCombination_UplinkTxSwitch_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition BandCombination_UplinkTxSwitch_r16__ext0__Format : T_Format BandCombination_UplinkTxSwitch_r16__ext0__Type BandCombination_UplinkTxSwitch_r16__ext0__cond :=
  restrict_add_format BandCombination_UplinkTxSwitch_r16__ext0__check_all_none BandCombination_UplinkTxSwitch_r16__ext0O__Format.

Opaque BandCombination_UplinkTxSwitch_r16__ext0__cond BandCombination_UplinkTxSwitch_r16__ext0__Format.


Definition BandCombination_UplinkTxSwitch_r16__root_Format_Type := Eval cbn in seq_format_prod BandCombination_UplinkTxSwitch_r16__root_list.
Definition BandCombination_UplinkTxSwitch_r16__root_Format_list : BandCombination_UplinkTxSwitch_r16__root_Format_Type :=
  (BandCombination__Format, (BandCombination_v1540__Format, (BandCombination_v1560__Format, (BandCombination_v1570__Format, (BandCombination_v1580__Format, (BandCombination_v1590__Format, (BandCombination_v1610__Format, (BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16__Format, (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16__Format, (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16__Format, unit_format)))))))))).

Definition BandCombination_UplinkTxSwitch_r16__ext_Format_Type := Eval cbn in get_formats BandCombination_UplinkTxSwitch_r16__ext_list.
Definition BandCombination_UplinkTxSwitch_r16__ext_Format_list : BandCombination_UplinkTxSwitch_r16__ext_Format_Type :=
  (BandCombination_UplinkTxSwitch_r16__ext0__Format, unit__Format).

Definition BandCombination_UplinkTxSwitch_r16__list_type : Set := (seq_type BandCombination_UplinkTxSwitch_r16__root_list) * (seq_ext_type BandCombination_UplinkTxSwitch_r16__ext_list).
Definition BandCombination_UplinkTxSwitch_r16__list_cond (z : BandCombination_UplinkTxSwitch_r16__list_type) : Prop :=
        (seq_cond BandCombination_UplinkTxSwitch_r16__root_list (fst z)) /\ (seq_ext_cond BandCombination_UplinkTxSwitch_r16__ext_list (snd z)).
Definition BandCombination_UplinkTxSwitch_r16__list_format : T_Format BandCombination_UplinkTxSwitch_r16__list_type BandCombination_UplinkTxSwitch_r16__list_cond :=
 (* Eval compute in *) seq_ext_format BandCombination_UplinkTxSwitch_r16__root_list BandCombination_UplinkTxSwitch_r16__root_Format_list BandCombination_UplinkTxSwitch_r16__ext_list BandCombination_UplinkTxSwitch_r16__ext_Format_list.

Opaque BandCombination_UplinkTxSwitch_r16__list_format.
Definition BandCombination_UplinkTxSwitch_r16__F1 (z : BandCombination_UplinkTxSwitch_r16__Type) : BandCombination_UplinkTxSwitch_r16__list_type :=
  (((BandCombination_UplinkTxSwitch_r16__bandCombination_r16 z, (BandCombination_UplinkTxSwitch_r16__bandCombination_v1540 z, (BandCombination_UplinkTxSwitch_r16__bandCombination_v1560 z, (BandCombination_UplinkTxSwitch_r16__bandCombination_v1570 z, (BandCombination_UplinkTxSwitch_r16__bandCombination_v1580 z, (BandCombination_UplinkTxSwitch_r16__bandCombination_v1590 z, (BandCombination_UplinkTxSwitch_r16__bandCombination_v1610 z, (BandCombination_UplinkTxSwitch_r16__supportedBandPairListNR_r16 z, (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_OptionSupport_r16 z, (BandCombination_UplinkTxSwitch_r16__uplinkTxSwitching_PowerBoosting_r16 z, tt))))))))))), (
(BandCombination_UplinkTxSwitch_r16__ext0 z, tt))).
Definition BandCombination_UplinkTxSwitch_r16__F2 (y : BandCombination_UplinkTxSwitch_r16__list_type) : BandCombination_UplinkTxSwitch_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, _)))))))))), (i0, _))=>
    make__BandCombination_UplinkTxSwitch_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i0
  end.
Definition BandCombination_UplinkTxSwitch_r16__helper1 : (forall a : BandCombination_UplinkTxSwitch_r16__Type, BandCombination_UplinkTxSwitch_r16__cond a -> BandCombination_UplinkTxSwitch_r16__list_cond (BandCombination_UplinkTxSwitch_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BandCombination_UplinkTxSwitch_r16__helper2 : (forall a : BandCombination_UplinkTxSwitch_r16__Type, BandCombination_UplinkTxSwitch_r16__F2 (BandCombination_UplinkTxSwitch_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BandCombination_UplinkTxSwitch_r16__helper3 : (forall b : BandCombination_UplinkTxSwitch_r16__list_type, BandCombination_UplinkTxSwitch_r16__list_cond b -> BandCombination_UplinkTxSwitch_r16__cond (BandCombination_UplinkTxSwitch_r16__F2 b) /\ BandCombination_UplinkTxSwitch_r16__F1 (BandCombination_UplinkTxSwitch_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BandCombination_UplinkTxSwitch_r16__cond, BandCombination_UplinkTxSwitch_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BandCombination_UplinkTxSwitch_r16__Format : T_Format BandCombination_UplinkTxSwitch_r16__Type BandCombination_UplinkTxSwitch_r16__cond :=
 proj2_format BandCombination_UplinkTxSwitch_r16__cond BandCombination_UplinkTxSwitch_r16__list_format  BandCombination_UplinkTxSwitch_r16__F1 BandCombination_UplinkTxSwitch_r16__F2 BandCombination_UplinkTxSwitch_r16__helper1 BandCombination_UplinkTxSwitch_r16__helper2 BandCombination_UplinkTxSwitch_r16__helper3.

Opaque BandCombination_UplinkTxSwitch_r16__cond BandCombination_UplinkTxSwitch_r16__Format.

