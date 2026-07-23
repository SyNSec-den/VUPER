Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasGapId_r17.

Opaque MeasGapId_r17__cond MeasGapId_r17__Format.

Inductive GapConfig_r17__gapType_r17__Type : Set :=
 | GapConfig_r17__gapType_r17__perUE
 | GapConfig_r17__gapType_r17__perFR1
 | GapConfig_r17__gapType_r17__perFR2
.
Definition GapConfig_r17__gapType_r17__cond := (fun (_ : GapConfig_r17__gapType_r17__Type) => True).
Lemma GapConfig_r17__gapType_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig_r17__gapType_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 GapConfig_r17__gapType_r17__nat__helper.

Definition GapConfig_r17__gapType_r17__F1 t :=
  match t with
  | GapConfig_r17__gapType_r17__perUE => 0
  | GapConfig_r17__gapType_r17__perFR1 => 1
  | GapConfig_r17__gapType_r17__perFR2 => 2
  end.
Definition GapConfig_r17__gapType_r17__F2 n :=
  match n with
  | 0 => GapConfig_r17__gapType_r17__perUE
  | 1 => GapConfig_r17__gapType_r17__perFR1
  | 2 => GapConfig_r17__gapType_r17__perFR2
  | _ => GapConfig_r17__gapType_r17__perUE
  end.
Lemma GapConfig_r17__gapType_r17__F1F2 : forall x : GapConfig_r17__gapType_r17__Type, (GapConfig_r17__gapType_r17__F1 x <= 2) /\ GapConfig_r17__gapType_r17__F2 (GapConfig_r17__gapType_r17__F1 x) = x. imp_solve. Qed.
Lemma GapConfig_r17__gapType_r17__F2F1 : forall (y : nat) (H : y <= 2), GapConfig_r17__gapType_r17__F1 (GapConfig_r17__gapType_r17__F2 y) = y. enum_solve H y. Qed.

Lemma GapConfig_r17__gapOffset_r17__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma GapConfig_r17__gapOffset_r17__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply GapConfig_r17__gapOffset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition GapConfig_r17__gapOffset_r17__Type := Z.
Definition GapConfig_r17__gapOffset_r17__cond := (fun z => (0 <= z <= 159)%Z).
Inductive GapConfig_r17__mgl_r17__Type : Set :=
 | GapConfig_r17__mgl_r17__ms1
 | GapConfig_r17__mgl_r17__ms1dot5
 | GapConfig_r17__mgl_r17__ms2
 | GapConfig_r17__mgl_r17__ms3
 | GapConfig_r17__mgl_r17__ms3dot5
 | GapConfig_r17__mgl_r17__ms4
 | GapConfig_r17__mgl_r17__ms5
 | GapConfig_r17__mgl_r17__ms5dot5
 | GapConfig_r17__mgl_r17__ms6
 | GapConfig_r17__mgl_r17__ms10
 | GapConfig_r17__mgl_r17__ms20
.
Definition GapConfig_r17__mgl_r17__cond := (fun (_ : GapConfig_r17__mgl_r17__Type) => True).
Lemma GapConfig_r17__mgl_r17__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig_r17__mgl_r17__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 GapConfig_r17__mgl_r17__nat__helper.

Definition GapConfig_r17__mgl_r17__F1 t :=
  match t with
  | GapConfig_r17__mgl_r17__ms1 => 0
  | GapConfig_r17__mgl_r17__ms1dot5 => 1
  | GapConfig_r17__mgl_r17__ms2 => 2
  | GapConfig_r17__mgl_r17__ms3 => 3
  | GapConfig_r17__mgl_r17__ms3dot5 => 4
  | GapConfig_r17__mgl_r17__ms4 => 5
  | GapConfig_r17__mgl_r17__ms5 => 6
  | GapConfig_r17__mgl_r17__ms5dot5 => 7
  | GapConfig_r17__mgl_r17__ms6 => 8
  | GapConfig_r17__mgl_r17__ms10 => 9
  | GapConfig_r17__mgl_r17__ms20 => 10
  end.
Definition GapConfig_r17__mgl_r17__F2 n :=
  match n with
  | 0 => GapConfig_r17__mgl_r17__ms1
  | 1 => GapConfig_r17__mgl_r17__ms1dot5
  | 2 => GapConfig_r17__mgl_r17__ms2
  | 3 => GapConfig_r17__mgl_r17__ms3
  | 4 => GapConfig_r17__mgl_r17__ms3dot5
  | 5 => GapConfig_r17__mgl_r17__ms4
  | 6 => GapConfig_r17__mgl_r17__ms5
  | 7 => GapConfig_r17__mgl_r17__ms5dot5
  | 8 => GapConfig_r17__mgl_r17__ms6
  | 9 => GapConfig_r17__mgl_r17__ms10
  | 10 => GapConfig_r17__mgl_r17__ms20
  | _ => GapConfig_r17__mgl_r17__ms1
  end.
Lemma GapConfig_r17__mgl_r17__F1F2 : forall x : GapConfig_r17__mgl_r17__Type, (GapConfig_r17__mgl_r17__F1 x <= 10) /\ GapConfig_r17__mgl_r17__F2 (GapConfig_r17__mgl_r17__F1 x) = x. imp_solve. Qed.
Lemma GapConfig_r17__mgl_r17__F2F1 : forall (y : nat) (H : y <= 10), GapConfig_r17__mgl_r17__F1 (GapConfig_r17__mgl_r17__F2 y) = y. enum_solve H y. Qed.

Inductive GapConfig_r17__mgrp_r17__Type : Set :=
 | GapConfig_r17__mgrp_r17__ms20
 | GapConfig_r17__mgrp_r17__ms40
 | GapConfig_r17__mgrp_r17__ms80
 | GapConfig_r17__mgrp_r17__ms160
.
Definition GapConfig_r17__mgrp_r17__cond := (fun (_ : GapConfig_r17__mgrp_r17__Type) => True).
Lemma GapConfig_r17__mgrp_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig_r17__mgrp_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 GapConfig_r17__mgrp_r17__nat__helper.

Definition GapConfig_r17__mgrp_r17__F1 t :=
  match t with
  | GapConfig_r17__mgrp_r17__ms20 => 0
  | GapConfig_r17__mgrp_r17__ms40 => 1
  | GapConfig_r17__mgrp_r17__ms80 => 2
  | GapConfig_r17__mgrp_r17__ms160 => 3
  end.
Definition GapConfig_r17__mgrp_r17__F2 n :=
  match n with
  | 0 => GapConfig_r17__mgrp_r17__ms20
  | 1 => GapConfig_r17__mgrp_r17__ms40
  | 2 => GapConfig_r17__mgrp_r17__ms80
  | 3 => GapConfig_r17__mgrp_r17__ms160
  | _ => GapConfig_r17__mgrp_r17__ms20
  end.
Lemma GapConfig_r17__mgrp_r17__F1F2 : forall x : GapConfig_r17__mgrp_r17__Type, (GapConfig_r17__mgrp_r17__F1 x <= 3) /\ GapConfig_r17__mgrp_r17__F2 (GapConfig_r17__mgrp_r17__F1 x) = x. imp_solve. Qed.
Lemma GapConfig_r17__mgrp_r17__F2F1 : forall (y : nat) (H : y <= 3), GapConfig_r17__mgrp_r17__F1 (GapConfig_r17__mgrp_r17__F2 y) = y. enum_solve H y. Qed.

Inductive GapConfig_r17__mgta_r17__Type : Set :=
 | GapConfig_r17__mgta_r17__ms0
 | GapConfig_r17__mgta_r17__ms0dot25
 | GapConfig_r17__mgta_r17__ms0dot5
 | GapConfig_r17__mgta_r17__ms0dot75
.
Definition GapConfig_r17__mgta_r17__cond := (fun (_ : GapConfig_r17__mgta_r17__Type) => True).
Lemma GapConfig_r17__mgta_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig_r17__mgta_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 GapConfig_r17__mgta_r17__nat__helper.

Definition GapConfig_r17__mgta_r17__F1 t :=
  match t with
  | GapConfig_r17__mgta_r17__ms0 => 0
  | GapConfig_r17__mgta_r17__ms0dot25 => 1
  | GapConfig_r17__mgta_r17__ms0dot5 => 2
  | GapConfig_r17__mgta_r17__ms0dot75 => 3
  end.
Definition GapConfig_r17__mgta_r17__F2 n :=
  match n with
  | 0 => GapConfig_r17__mgta_r17__ms0
  | 1 => GapConfig_r17__mgta_r17__ms0dot25
  | 2 => GapConfig_r17__mgta_r17__ms0dot5
  | 3 => GapConfig_r17__mgta_r17__ms0dot75
  | _ => GapConfig_r17__mgta_r17__ms0
  end.
Lemma GapConfig_r17__mgta_r17__F1F2 : forall x : GapConfig_r17__mgta_r17__Type, (GapConfig_r17__mgta_r17__F1 x <= 3) /\ GapConfig_r17__mgta_r17__F2 (GapConfig_r17__mgta_r17__F1 x) = x. imp_solve. Qed.
Lemma GapConfig_r17__mgta_r17__F2F1 : forall (y : nat) (H : y <= 3), GapConfig_r17__mgta_r17__F1 (GapConfig_r17__mgta_r17__F2 y) = y. enum_solve H y. Qed.

Inductive GapConfig_r17__refServCellIndicator_r17__Type : Set :=
 | GapConfig_r17__refServCellIndicator_r17__pCell
 | GapConfig_r17__refServCellIndicator_r17__pSCell
 | GapConfig_r17__refServCellIndicator_r17__mcg_FR2
.
Definition GapConfig_r17__refServCellIndicator_r17__cond := (fun (_ : GapConfig_r17__refServCellIndicator_r17__Type) => True).
Lemma GapConfig_r17__refServCellIndicator_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig_r17__refServCellIndicator_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 GapConfig_r17__refServCellIndicator_r17__nat__helper.

Definition GapConfig_r17__refServCellIndicator_r17__F1 t :=
  match t with
  | GapConfig_r17__refServCellIndicator_r17__pCell => 0
  | GapConfig_r17__refServCellIndicator_r17__pSCell => 1
  | GapConfig_r17__refServCellIndicator_r17__mcg_FR2 => 2
  end.
Definition GapConfig_r17__refServCellIndicator_r17__F2 n :=
  match n with
  | 0 => GapConfig_r17__refServCellIndicator_r17__pCell
  | 1 => GapConfig_r17__refServCellIndicator_r17__pSCell
  | 2 => GapConfig_r17__refServCellIndicator_r17__mcg_FR2
  | _ => GapConfig_r17__refServCellIndicator_r17__pCell
  end.
Lemma GapConfig_r17__refServCellIndicator_r17__F1F2 : forall x : GapConfig_r17__refServCellIndicator_r17__Type, (GapConfig_r17__refServCellIndicator_r17__F1 x <= 2) /\ GapConfig_r17__refServCellIndicator_r17__F2 (GapConfig_r17__refServCellIndicator_r17__F1 x) = x. imp_solve. Qed.
Lemma GapConfig_r17__refServCellIndicator_r17__F2F1 : forall (y : nat) (H : y <= 2), GapConfig_r17__refServCellIndicator_r17__F1 (GapConfig_r17__refServCellIndicator_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Inductive GapConfig_r17__preConfigInd_r17__Type : Set :=
 | GapConfig_r17__preConfigInd_r17__true
.
Definition GapConfig_r17__preConfigInd_r17__cond := (fun (_ : GapConfig_r17__preConfigInd_r17__Type) => True).
Lemma GapConfig_r17__preConfigInd_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig_r17__preConfigInd_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 GapConfig_r17__preConfigInd_r17__nat__helper.

Definition GapConfig_r17__preConfigInd_r17__F1 t :=
  match t with
  | GapConfig_r17__preConfigInd_r17__true => 0
  end.
Definition GapConfig_r17__preConfigInd_r17__F2 n :=
  match n with
  | 0 => GapConfig_r17__preConfigInd_r17__true
  | _ => GapConfig_r17__preConfigInd_r17__true
  end.
Lemma GapConfig_r17__preConfigInd_r17__F1F2 : forall x : GapConfig_r17__preConfigInd_r17__Type, (GapConfig_r17__preConfigInd_r17__F1 x <= 0) /\ GapConfig_r17__preConfigInd_r17__F2 (GapConfig_r17__preConfigInd_r17__F1 x) = x. imp_solve. Qed.
Lemma GapConfig_r17__preConfigInd_r17__F2F1 : forall (y : nat) (H : y <= 0), GapConfig_r17__preConfigInd_r17__F1 (GapConfig_r17__preConfigInd_r17__F2 y) = y. enum_solve H y. Qed.

Inductive GapConfig_r17__ncsgInd_r17__Type : Set :=
 | GapConfig_r17__ncsgInd_r17__true
.
Definition GapConfig_r17__ncsgInd_r17__cond := (fun (_ : GapConfig_r17__ncsgInd_r17__Type) => True).
Lemma GapConfig_r17__ncsgInd_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig_r17__ncsgInd_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 GapConfig_r17__ncsgInd_r17__nat__helper.

Definition GapConfig_r17__ncsgInd_r17__F1 t :=
  match t with
  | GapConfig_r17__ncsgInd_r17__true => 0
  end.
Definition GapConfig_r17__ncsgInd_r17__F2 n :=
  match n with
  | 0 => GapConfig_r17__ncsgInd_r17__true
  | _ => GapConfig_r17__ncsgInd_r17__true
  end.
Lemma GapConfig_r17__ncsgInd_r17__F1F2 : forall x : GapConfig_r17__ncsgInd_r17__Type, (GapConfig_r17__ncsgInd_r17__F1 x <= 0) /\ GapConfig_r17__ncsgInd_r17__F2 (GapConfig_r17__ncsgInd_r17__F1 x) = x. imp_solve. Qed.
Lemma GapConfig_r17__ncsgInd_r17__F2F1 : forall (y : nat) (H : y <= 0), GapConfig_r17__ncsgInd_r17__F1 (GapConfig_r17__ncsgInd_r17__F2 y) = y. enum_solve H y. Qed.

Inductive GapConfig_r17__gapAssociationPRS_r17__Type : Set :=
 | GapConfig_r17__gapAssociationPRS_r17__true
.
Definition GapConfig_r17__gapAssociationPRS_r17__cond := (fun (_ : GapConfig_r17__gapAssociationPRS_r17__Type) => True).
Lemma GapConfig_r17__gapAssociationPRS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GapConfig_r17__gapAssociationPRS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 GapConfig_r17__gapAssociationPRS_r17__nat__helper.

Definition GapConfig_r17__gapAssociationPRS_r17__F1 t :=
  match t with
  | GapConfig_r17__gapAssociationPRS_r17__true => 0
  end.
Definition GapConfig_r17__gapAssociationPRS_r17__F2 n :=
  match n with
  | 0 => GapConfig_r17__gapAssociationPRS_r17__true
  | _ => GapConfig_r17__gapAssociationPRS_r17__true
  end.
Lemma GapConfig_r17__gapAssociationPRS_r17__F1F2 : forall x : GapConfig_r17__gapAssociationPRS_r17__Type, (GapConfig_r17__gapAssociationPRS_r17__F1 x <= 0) /\ GapConfig_r17__gapAssociationPRS_r17__F2 (GapConfig_r17__gapAssociationPRS_r17__F1 x) = x. imp_solve. Qed.
Lemma GapConfig_r17__gapAssociationPRS_r17__F2F1 : forall (y : nat) (H : y <= 0), GapConfig_r17__gapAssociationPRS_r17__F1 (GapConfig_r17__gapAssociationPRS_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasGapSharingScheme.

Opaque MeasGapSharingScheme__cond MeasGapSharingScheme__Format.

Require Import NR.GapPriority_r17.

Opaque GapPriority_r17__cond GapPriority_r17__Format.

Record GapConfig_r17__Type : Set :=
  make__GapConfig_r17__Type {
    GapConfig_r17__measGapId_r17 : MeasGapId_r17__Type ;
    GapConfig_r17__gapType_r17 : GapConfig_r17__gapType_r17__Type ;
    GapConfig_r17__gapOffset_r17 : Z ;
    GapConfig_r17__mgl_r17 : GapConfig_r17__mgl_r17__Type ;
    GapConfig_r17__mgrp_r17 : GapConfig_r17__mgrp_r17__Type ;
    GapConfig_r17__mgta_r17 : GapConfig_r17__mgta_r17__Type ;
    GapConfig_r17__refServCellIndicator_r17 : option GapConfig_r17__refServCellIndicator_r17__Type ;
    GapConfig_r17__refFR2_ServCellAsyncCA_r17 : option ServCellIndex__Type ;
    GapConfig_r17__preConfigInd_r17 : option GapConfig_r17__preConfigInd_r17__Type ;
    GapConfig_r17__ncsgInd_r17 : option GapConfig_r17__ncsgInd_r17__Type ;
    GapConfig_r17__gapAssociationPRS_r17 : option GapConfig_r17__gapAssociationPRS_r17__Type ;
    GapConfig_r17__gapSharing_r17 : option MeasGapSharingScheme__Type ;
    GapConfig_r17__gapPriority_r17 : option GapPriority_r17__Type ;
}.
Definition GapConfig_r17__root_list : list seq_elem := (
 Nor MeasGapId_r17__Type MeasGapId_r17__cond ::
 Nor GapConfig_r17__gapType_r17__Type GapConfig_r17__gapType_r17__cond ::
 Nor Z GapConfig_r17__gapOffset_r17__cond ::
 Nor GapConfig_r17__mgl_r17__Type GapConfig_r17__mgl_r17__cond ::
 Nor GapConfig_r17__mgrp_r17__Type GapConfig_r17__mgrp_r17__cond ::
 Nor GapConfig_r17__mgta_r17__Type GapConfig_r17__mgta_r17__cond ::
 Opt GapConfig_r17__refServCellIndicator_r17__Type GapConfig_r17__refServCellIndicator_r17__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Opt GapConfig_r17__preConfigInd_r17__Type GapConfig_r17__preConfigInd_r17__cond ::
 Opt GapConfig_r17__ncsgInd_r17__Type GapConfig_r17__ncsgInd_r17__cond ::
 Opt GapConfig_r17__gapAssociationPRS_r17__Type GapConfig_r17__gapAssociationPRS_r17__cond ::
 Opt MeasGapSharingScheme__Type MeasGapSharingScheme__cond ::
 Opt GapPriority_r17__Type GapPriority_r17__cond ::
 nil).
Definition GapConfig_r17__ext_list : list typ := (
  nil).
Definition GapConfig_r17__cond (z : GapConfig_r17__Type) := 
(  MeasGapId_r17__cond (GapConfig_r17__measGapId_r17 z) /\
  GapConfig_r17__gapType_r17__cond (GapConfig_r17__gapType_r17 z) /\
  GapConfig_r17__gapOffset_r17__cond (GapConfig_r17__gapOffset_r17 z) /\
  GapConfig_r17__mgl_r17__cond (GapConfig_r17__mgl_r17 z) /\
  GapConfig_r17__mgrp_r17__cond (GapConfig_r17__mgrp_r17 z) /\
  GapConfig_r17__mgta_r17__cond (GapConfig_r17__mgta_r17 z) /\
  opt_cond GapConfig_r17__refServCellIndicator_r17__cond (GapConfig_r17__refServCellIndicator_r17 z) /\
  opt_cond ServCellIndex__cond (GapConfig_r17__refFR2_ServCellAsyncCA_r17 z) /\
  opt_cond GapConfig_r17__preConfigInd_r17__cond (GapConfig_r17__preConfigInd_r17 z) /\
  opt_cond GapConfig_r17__ncsgInd_r17__cond (GapConfig_r17__ncsgInd_r17 z) /\
  opt_cond GapConfig_r17__gapAssociationPRS_r17__cond (GapConfig_r17__gapAssociationPRS_r17 z) /\
  opt_cond MeasGapSharingScheme__cond (GapConfig_r17__gapSharing_r17 z) /\
  opt_cond GapPriority_r17__cond (GapConfig_r17__gapPriority_r17 z) /\
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
Definition GapConfig_r17__gapType_r17__Format : T_Format GapConfig_r17__gapType_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig_r17__gapType_r17__nat__Format GapConfig_r17__gapType_r17__F1 GapConfig_r17__gapType_r17__F2 GapConfig_r17__gapType_r17__F1F2 GapConfig_r17__gapType_r17__F2F1.

Opaque GapConfig_r17__gapType_r17__cond GapConfig_r17__gapType_r17__Format.

Definition GapConfig_r17__gapOffset_r17__Format : T_Format Z GapConfig_r17__gapOffset_r17__cond :=
 ranged_int_format (0) (159) GapConfig_r17__gapOffset_r17__helper1 GapConfig_r17__gapOffset_r17__helper2.

Opaque GapConfig_r17__gapOffset_r17__cond GapConfig_r17__gapOffset_r17__Format.

Definition GapConfig_r17__mgl_r17__Format : T_Format GapConfig_r17__mgl_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig_r17__mgl_r17__nat__Format GapConfig_r17__mgl_r17__F1 GapConfig_r17__mgl_r17__F2 GapConfig_r17__mgl_r17__F1F2 GapConfig_r17__mgl_r17__F2F1.

Opaque GapConfig_r17__mgl_r17__cond GapConfig_r17__mgl_r17__Format.

Definition GapConfig_r17__mgrp_r17__Format : T_Format GapConfig_r17__mgrp_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig_r17__mgrp_r17__nat__Format GapConfig_r17__mgrp_r17__F1 GapConfig_r17__mgrp_r17__F2 GapConfig_r17__mgrp_r17__F1F2 GapConfig_r17__mgrp_r17__F2F1.

Opaque GapConfig_r17__mgrp_r17__cond GapConfig_r17__mgrp_r17__Format.

Definition GapConfig_r17__mgta_r17__Format : T_Format GapConfig_r17__mgta_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig_r17__mgta_r17__nat__Format GapConfig_r17__mgta_r17__F1 GapConfig_r17__mgta_r17__F2 GapConfig_r17__mgta_r17__F1F2 GapConfig_r17__mgta_r17__F2F1.

Opaque GapConfig_r17__mgta_r17__cond GapConfig_r17__mgta_r17__Format.

Definition GapConfig_r17__refServCellIndicator_r17__Format : T_Format GapConfig_r17__refServCellIndicator_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig_r17__refServCellIndicator_r17__nat__Format GapConfig_r17__refServCellIndicator_r17__F1 GapConfig_r17__refServCellIndicator_r17__F2 GapConfig_r17__refServCellIndicator_r17__F1F2 GapConfig_r17__refServCellIndicator_r17__F2F1.

Opaque GapConfig_r17__refServCellIndicator_r17__cond GapConfig_r17__refServCellIndicator_r17__Format.

Definition GapConfig_r17__preConfigInd_r17__Format : T_Format GapConfig_r17__preConfigInd_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig_r17__preConfigInd_r17__nat__Format GapConfig_r17__preConfigInd_r17__F1 GapConfig_r17__preConfigInd_r17__F2 GapConfig_r17__preConfigInd_r17__F1F2 GapConfig_r17__preConfigInd_r17__F2F1.

Opaque GapConfig_r17__preConfigInd_r17__cond GapConfig_r17__preConfigInd_r17__Format.

Definition GapConfig_r17__ncsgInd_r17__Format : T_Format GapConfig_r17__ncsgInd_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig_r17__ncsgInd_r17__nat__Format GapConfig_r17__ncsgInd_r17__F1 GapConfig_r17__ncsgInd_r17__F2 GapConfig_r17__ncsgInd_r17__F1F2 GapConfig_r17__ncsgInd_r17__F2F1.

Opaque GapConfig_r17__ncsgInd_r17__cond GapConfig_r17__ncsgInd_r17__Format.

Definition GapConfig_r17__gapAssociationPRS_r17__Format : T_Format GapConfig_r17__gapAssociationPRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GapConfig_r17__gapAssociationPRS_r17__nat__Format GapConfig_r17__gapAssociationPRS_r17__F1 GapConfig_r17__gapAssociationPRS_r17__F2 GapConfig_r17__gapAssociationPRS_r17__F1F2 GapConfig_r17__gapAssociationPRS_r17__F2F1.

Opaque GapConfig_r17__gapAssociationPRS_r17__cond GapConfig_r17__gapAssociationPRS_r17__Format.


Definition GapConfig_r17__root_Format_Type := Eval cbn in seq_format_prod GapConfig_r17__root_list.
Definition GapConfig_r17__root_Format_list : GapConfig_r17__root_Format_Type :=
  (MeasGapId_r17__Format, (GapConfig_r17__gapType_r17__Format, (GapConfig_r17__gapOffset_r17__Format, (GapConfig_r17__mgl_r17__Format, (GapConfig_r17__mgrp_r17__Format, (GapConfig_r17__mgta_r17__Format, (GapConfig_r17__refServCellIndicator_r17__Format, (ServCellIndex__Format, (GapConfig_r17__preConfigInd_r17__Format, (GapConfig_r17__ncsgInd_r17__Format, (GapConfig_r17__gapAssociationPRS_r17__Format, (MeasGapSharingScheme__Format, (GapPriority_r17__Format, unit_format))))))))))))).

Definition GapConfig_r17__ext_Format_Type := Eval cbn in get_formats GapConfig_r17__ext_list.
Definition GapConfig_r17__ext_Format_list : GapConfig_r17__ext_Format_Type :=
  unit__Format.

Definition GapConfig_r17__list_type : Set := (seq_type GapConfig_r17__root_list) * (seq_ext_type GapConfig_r17__ext_list).
Definition GapConfig_r17__list_cond (z : GapConfig_r17__list_type) : Prop :=
        (seq_cond GapConfig_r17__root_list (fst z)) /\ (seq_ext_cond GapConfig_r17__ext_list (snd z)).
Definition GapConfig_r17__list_format : T_Format GapConfig_r17__list_type GapConfig_r17__list_cond :=
 (* Eval compute in *) seq_ext_format GapConfig_r17__root_list GapConfig_r17__root_Format_list GapConfig_r17__ext_list GapConfig_r17__ext_Format_list.

Opaque GapConfig_r17__list_format.
Definition GapConfig_r17__F1 (z : GapConfig_r17__Type) : GapConfig_r17__list_type :=
  (((GapConfig_r17__measGapId_r17 z, (GapConfig_r17__gapType_r17 z, (GapConfig_r17__gapOffset_r17 z, (GapConfig_r17__mgl_r17 z, (GapConfig_r17__mgrp_r17 z, (GapConfig_r17__mgta_r17 z, (GapConfig_r17__refServCellIndicator_r17 z, (GapConfig_r17__refFR2_ServCellAsyncCA_r17 z, (GapConfig_r17__preConfigInd_r17 z, (GapConfig_r17__ncsgInd_r17 z, (GapConfig_r17__gapAssociationPRS_r17 z, (GapConfig_r17__gapSharing_r17 z, (GapConfig_r17__gapPriority_r17 z, tt)))))))))))))), (
tt)).
Definition GapConfig_r17__F2 (y : GapConfig_r17__list_type) : GapConfig_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, _))))))))))))), _)=>
    make__GapConfig_r17__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12
  end.
Definition GapConfig_r17__helper1 : (forall a : GapConfig_r17__Type, GapConfig_r17__cond a -> GapConfig_r17__list_cond (GapConfig_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition GapConfig_r17__helper2 : (forall a : GapConfig_r17__Type, GapConfig_r17__F2 (GapConfig_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition GapConfig_r17__helper3 : (forall b : GapConfig_r17__list_type, GapConfig_r17__list_cond b -> GapConfig_r17__cond (GapConfig_r17__F2 b) /\ GapConfig_r17__F1 (GapConfig_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold GapConfig_r17__cond, GapConfig_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition GapConfig_r17__Format : T_Format GapConfig_r17__Type GapConfig_r17__cond :=
 proj2_format GapConfig_r17__cond GapConfig_r17__list_format  GapConfig_r17__F1 GapConfig_r17__F2 GapConfig_r17__helper1 GapConfig_r17__helper2 GapConfig_r17__helper3.

Opaque GapConfig_r17__cond GapConfig_r17__Format.

