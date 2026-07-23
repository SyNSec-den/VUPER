Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Record CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type : Set :=
  make__CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type {
    CrossCarrierSchedulingConfig__schedulingCellInfo__own__cif_Presence : bool ;
}.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__own__list := (
 Nor bool (fun _ => True) ::
 nil).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond z := 
  (fun _ => True) (CrossCarrierSchedulingConfig__schedulingCellInfo__own__cif_Presence z) /\
  True.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__helper1 : (1 <= 7)%Z.  lia. Qed.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__helper2 : to_bit_sz (Z.to_nat (7 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__Type := Z.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__cond := (fun z => (1 <= z <= 7)%Z).
Record CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type : Set :=
  make__CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type {
    CrossCarrierSchedulingConfig__schedulingCellInfo__other__schedulingCellId : ServCellIndex__Type ;
    CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell : Z ;
}.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor Z CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__cond ::
 nil).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond z := 
  ServCellIndex__cond (CrossCarrierSchedulingConfig__schedulingCellInfo__other__schedulingCellId z) /\
  CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__cond (CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell z) /\
  True.


Inductive CrossCarrierSchedulingConfig__schedulingCellInfo__Type : Set :=
  | CrossCarrierSchedulingConfig__schedulingCellInfo__own : CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type -> CrossCarrierSchedulingConfig__schedulingCellInfo__Type
  | CrossCarrierSchedulingConfig__schedulingCellInfo__other : CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type -> CrossCarrierSchedulingConfig__schedulingCellInfo__Type
.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__list : list typ := (
typ_cons CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond ::
typ_cons CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond ::
 nil).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__cond (c : CrossCarrierSchedulingConfig__schedulingCellInfo__Type) := 
  match c with
  | CrossCarrierSchedulingConfig__schedulingCellInfo__own t => CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond t 
  | CrossCarrierSchedulingConfig__schedulingCellInfo__other t => CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond t 
  end.

Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__len_helper1 : to_bit_sz (length CrossCarrierSchedulingConfig__schedulingCellInfo__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__len_helper2 : 2 <= length2 CrossCarrierSchedulingConfig__schedulingCellInfo__list.
 simpl. lia. Qed.
Lemma CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__Type := Z.
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__cond := (fun z => (0 <= z <= 3)%Z).
Lemma CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__Type := Z.
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__cond := (fun z => (0 <= z <= 3)%Z).
Record CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Type : Set :=
  make__CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Type {
    CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16 : Z ;
    CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16 : Z ;
}.
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list := (
 Nor Z CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__cond ::
 Nor Z CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__cond ::
 nil).
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond z := 
  CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__cond (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16 z) /\
  CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__cond (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16 z) /\
  True.

Inductive CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Type : Set :=
 | CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__enabled
.
Definition CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__cond := (fun (_ : CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Type) => True).
Lemma CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__nat__helper.

Definition CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F1 t :=
  match t with
  | CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__enabled => 0
  end.
Definition CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F2 n :=
  match n with
  | 0 => CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__enabled
  | _ => CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__enabled
  end.
Lemma CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F1F2 : forall x : CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Type, (CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F1 x <= 0) /\ CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F2 (CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F1 x) = x. imp_solve. Qed.
Lemma CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F2F1 : forall (y : nat) (H : y <= 0), CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F1 (CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F2 y) = y. enum_solve H y. Qed.

Record CrossCarrierSchedulingConfig__ext0O__Type : Set :=
  make__CrossCarrierSchedulingConfig__ext0O__Type {
    CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16 : option CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Type ;
    CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16 : option CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Type ;
}.
Definition CrossCarrierSchedulingConfig__ext0O__list := (
 Opt CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Type CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond ::
 Opt CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Type CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__cond ::
 nil).
Definition CrossCarrierSchedulingConfig__ext0O__cond z := 
  opt_cond CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16 z) /\
  opt_cond CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__cond (CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16 z) /\
  True.

Definition CrossCarrierSchedulingConfig__ext0__Type := CrossCarrierSchedulingConfig__ext0O__Type.
Definition CrossCarrierSchedulingConfig__ext0__cond := CrossCarrierSchedulingConfig__ext0O__cond.

Inductive CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Type : Set :=
 | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__oneSeventh
 | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__threeFourteenth
 | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__twoSeventh
 | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__threeSeventh
 | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__oneHalf
 | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__fourSeventh
 | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__fiveSeventh
 | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__spare1
.
Definition CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__cond := (fun (_ : CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Type) => True).
Lemma CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__nat__helper.

Definition CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F1 t :=
  match t with
  | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__oneSeventh => 0
  | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__threeFourteenth => 1
  | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__twoSeventh => 2
  | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__threeSeventh => 3
  | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__oneHalf => 4
  | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__fourSeventh => 5
  | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__fiveSeventh => 6
  | CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__spare1 => 7
  end.
Definition CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F2 n :=
  match n with
  | 0 => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__oneSeventh
  | 1 => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__threeFourteenth
  | 2 => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__twoSeventh
  | 3 => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__threeSeventh
  | 4 => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__oneHalf
  | 5 => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__fourSeventh
  | 6 => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__fiveSeventh
  | 7 => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__spare1
  | _ => CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__oneSeventh
  end.
Lemma CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F1F2 : forall x : CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Type, (CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F1 x <= 7) /\ CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F2 (CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F1 x) = x. imp_solve. Qed.
Lemma CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F2F1 : forall (y : nat) (H : y <= 7), CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F1 (CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F2 y) = y. enum_solve H y. Qed.

Record CrossCarrierSchedulingConfig__ext1O__Type : Set :=
  make__CrossCarrierSchedulingConfig__ext1O__Type {
    CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17 : option CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Type ;
}.
Definition CrossCarrierSchedulingConfig__ext1O__list := (
 Opt CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Type CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__cond ::
 nil).
Definition CrossCarrierSchedulingConfig__ext1O__cond z := 
  opt_cond CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__cond (CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17 z) /\
  True.

Definition CrossCarrierSchedulingConfig__ext1__Type := CrossCarrierSchedulingConfig__ext1O__Type.
Definition CrossCarrierSchedulingConfig__ext1__cond := CrossCarrierSchedulingConfig__ext1O__cond.

Record CrossCarrierSchedulingConfig__Type : Set :=
  make__CrossCarrierSchedulingConfig__Type {
    CrossCarrierSchedulingConfig__schedulingCellInfo : CrossCarrierSchedulingConfig__schedulingCellInfo__Type ;
    CrossCarrierSchedulingConfig__ext0 : option CrossCarrierSchedulingConfig__ext0__Type ;
    CrossCarrierSchedulingConfig__ext1 : option CrossCarrierSchedulingConfig__ext1__Type ;
}.
Definition CrossCarrierSchedulingConfig__root_list : list seq_elem := (
 Nor CrossCarrierSchedulingConfig__schedulingCellInfo__Type CrossCarrierSchedulingConfig__schedulingCellInfo__cond ::
 nil).
Definition CrossCarrierSchedulingConfig__ext_list : list typ := (
  typ_cons CrossCarrierSchedulingConfig__ext0__Type CrossCarrierSchedulingConfig__ext0__cond ::
  typ_cons CrossCarrierSchedulingConfig__ext1__Type CrossCarrierSchedulingConfig__ext1__cond ::
  nil).
Definition CrossCarrierSchedulingConfig__cond (z : CrossCarrierSchedulingConfig__Type) := 
(  CrossCarrierSchedulingConfig__schedulingCellInfo__cond (CrossCarrierSchedulingConfig__schedulingCellInfo z) /\
  True) /\ 
(  opt_cond CrossCarrierSchedulingConfig__ext0__cond (CrossCarrierSchedulingConfig__ext0 z) /\
  opt_cond CrossCarrierSchedulingConfig__ext1__cond (CrossCarrierSchedulingConfig__ext1 z) /\
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

Definition CrossCarrierSchedulingConfig__schedulingCellInfo__own__Format_Type := Eval cbn in seq_format_prod CrossCarrierSchedulingConfig__schedulingCellInfo__own__list.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__own__Format_list : CrossCarrierSchedulingConfig__schedulingCellInfo__own__Format_Type :=
  (bool__Format, unit_format).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__own__list__Format := (*Eval compute in *) seq_format CrossCarrierSchedulingConfig__schedulingCellInfo__own__list CrossCarrierSchedulingConfig__schedulingCellInfo__own__Format_list.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1 z :=
  (CrossCarrierSchedulingConfig__schedulingCellInfo__own__cif_Presence z, tt).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__own__F2 (y : seq_type CrossCarrierSchedulingConfig__schedulingCellInfo__own__list) :=
  match y with
  | (i0, _)=>
    make__CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type i0
  end.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1F2_cond (z : CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type)
  : CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond z ->
  (seq_cond CrossCarrierSchedulingConfig__schedulingCellInfo__own__list (CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1 z)).
intro H. unfold CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond in H. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1F2_cond2 (z : CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type)
 : CrossCarrierSchedulingConfig__schedulingCellInfo__own__F2 (CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__own__F2F1_cond (y : seq_type CrossCarrierSchedulingConfig__schedulingCellInfo__own__list)
  : seq_cond CrossCarrierSchedulingConfig__schedulingCellInfo__own__list y ->
 (CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond (CrossCarrierSchedulingConfig__schedulingCellInfo__own__F2 y)) /\  CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1 (CrossCarrierSchedulingConfig__schedulingCellInfo__own__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond. simpl in *. auto.
 - simpl. unfold CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__own__Format : T_Format CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond :=
        proj2_format  CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond CrossCarrierSchedulingConfig__schedulingCellInfo__own__list__Format
    CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1 CrossCarrierSchedulingConfig__schedulingCellInfo__own__F2 CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1F2_cond  CrossCarrierSchedulingConfig__schedulingCellInfo__own__F1F2_cond2 CrossCarrierSchedulingConfig__schedulingCellInfo__own__F2F1_cond.
Opaque CrossCarrierSchedulingConfig__schedulingCellInfo__own__cond CrossCarrierSchedulingConfig__schedulingCellInfo__own__Format.

Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__Format : T_Format Z CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__cond :=
 ranged_int_format (1) (7) CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__helper1 CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__helper2.

Opaque CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__cond CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__Format.


Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__Format_Type := Eval cbn in seq_format_prod CrossCarrierSchedulingConfig__schedulingCellInfo__other__list.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__Format_list : CrossCarrierSchedulingConfig__schedulingCellInfo__other__Format_Type :=
  (ServCellIndex__Format, (CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell__Format, unit_format)).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__list__Format := (*Eval compute in *) seq_format CrossCarrierSchedulingConfig__schedulingCellInfo__other__list CrossCarrierSchedulingConfig__schedulingCellInfo__other__Format_list.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1 z :=
  (CrossCarrierSchedulingConfig__schedulingCellInfo__other__schedulingCellId z, (CrossCarrierSchedulingConfig__schedulingCellInfo__other__cif_InSchedulingCell z, tt)).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__F2 (y : seq_type CrossCarrierSchedulingConfig__schedulingCellInfo__other__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type i0 i1
  end.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1F2_cond (z : CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type)
  : CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond z ->
  (seq_cond CrossCarrierSchedulingConfig__schedulingCellInfo__other__list (CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1 z)).
intro H. unfold CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond in H. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1F2_cond2 (z : CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type)
 : CrossCarrierSchedulingConfig__schedulingCellInfo__other__F2 (CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__other__F2F1_cond (y : seq_type CrossCarrierSchedulingConfig__schedulingCellInfo__other__list)
  : seq_cond CrossCarrierSchedulingConfig__schedulingCellInfo__other__list y ->
 (CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond (CrossCarrierSchedulingConfig__schedulingCellInfo__other__F2 y)) /\  CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1 (CrossCarrierSchedulingConfig__schedulingCellInfo__other__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond. simpl in *. auto.
 - simpl. unfold CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__other__Format : T_Format CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond :=
        proj2_format  CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond CrossCarrierSchedulingConfig__schedulingCellInfo__other__list__Format
    CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1 CrossCarrierSchedulingConfig__schedulingCellInfo__other__F2 CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1F2_cond  CrossCarrierSchedulingConfig__schedulingCellInfo__other__F1F2_cond2 CrossCarrierSchedulingConfig__schedulingCellInfo__other__F2F1_cond.
Opaque CrossCarrierSchedulingConfig__schedulingCellInfo__other__cond CrossCarrierSchedulingConfig__schedulingCellInfo__other__Format.


Definition CrossCarrierSchedulingConfig__schedulingCellInfo__Format_Type := Eval cbn in get_formats CrossCarrierSchedulingConfig__schedulingCellInfo__list.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__Format_list : CrossCarrierSchedulingConfig__schedulingCellInfo__Format_Type :=
  (CrossCarrierSchedulingConfig__schedulingCellInfo__own__Format, (CrossCarrierSchedulingConfig__schedulingCellInfo__other__Format, unit__Format)).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__list__Format := Eval compute in choice_format CrossCarrierSchedulingConfig__schedulingCellInfo__list CrossCarrierSchedulingConfig__schedulingCellInfo__len_helper1 CrossCarrierSchedulingConfig__schedulingCellInfo__len_helper2  CrossCarrierSchedulingConfig__schedulingCellInfo__Format_list.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__F1 (z : CrossCarrierSchedulingConfig__schedulingCellInfo__Type) : (choice CrossCarrierSchedulingConfig__schedulingCellInfo__list) :=
  match z with
   | CrossCarrierSchedulingConfig__schedulingCellInfo__own t => existT _ 0 t
  | CrossCarrierSchedulingConfig__schedulingCellInfo__other t => existT _ 1 t
  end.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__g := (fun n => typ_set (get_nth_typ CrossCarrierSchedulingConfig__schedulingCellInfo__list n)).
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__F2 (y : choice CrossCarrierSchedulingConfig__schedulingCellInfo__list) : CrossCarrierSchedulingConfig__schedulingCellInfo__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CrossCarrierSchedulingConfig__schedulingCellInfo__g n -> CrossCarrierSchedulingConfig__schedulingCellInfo__Type) with
    | 0 => fun (t : CrossCarrierSchedulingConfig__schedulingCellInfo__own__Type) => CrossCarrierSchedulingConfig__schedulingCellInfo__own t 
    | 1 => fun (t : CrossCarrierSchedulingConfig__schedulingCellInfo__other__Type) => CrossCarrierSchedulingConfig__schedulingCellInfo__other t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CrossCarrierSchedulingConfig__schedulingCellInfo__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CrossCarrierSchedulingConfig__schedulingCellInfo__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CrossCarrierSchedulingConfig__schedulingCellInfo__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CrossCarrierSchedulingConfig__schedulingCellInfo__Type with end) n0
           end t0).

Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__helper2 :  forall (y : CrossCarrierSchedulingConfig__schedulingCellInfo__Type), CrossCarrierSchedulingConfig__schedulingCellInfo__cond y -> choice_cond CrossCarrierSchedulingConfig__schedulingCellInfo__list (CrossCarrierSchedulingConfig__schedulingCellInfo__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__helper3 :  forall (y : CrossCarrierSchedulingConfig__schedulingCellInfo__Type), CrossCarrierSchedulingConfig__schedulingCellInfo__F2 (CrossCarrierSchedulingConfig__schedulingCellInfo__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CrossCarrierSchedulingConfig__schedulingCellInfo__helper4 : (forall b : choice CrossCarrierSchedulingConfig__schedulingCellInfo__list, choice_cond CrossCarrierSchedulingConfig__schedulingCellInfo__list b -> CrossCarrierSchedulingConfig__schedulingCellInfo__cond (CrossCarrierSchedulingConfig__schedulingCellInfo__F2 b) /\ CrossCarrierSchedulingConfig__schedulingCellInfo__F1 (CrossCarrierSchedulingConfig__schedulingCellInfo__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CrossCarrierSchedulingConfig__schedulingCellInfo__F1 CrossCarrierSchedulingConfig__schedulingCellInfo__F2.
Definition CrossCarrierSchedulingConfig__schedulingCellInfo__Format : T_Format CrossCarrierSchedulingConfig__schedulingCellInfo__Type CrossCarrierSchedulingConfig__schedulingCellInfo__cond :=
  (* Eval compute in *) proj2_format CrossCarrierSchedulingConfig__schedulingCellInfo__cond CrossCarrierSchedulingConfig__schedulingCellInfo__list__Format CrossCarrierSchedulingConfig__schedulingCellInfo__F1 CrossCarrierSchedulingConfig__schedulingCellInfo__F2 CrossCarrierSchedulingConfig__schedulingCellInfo__helper2 CrossCarrierSchedulingConfig__schedulingCellInfo__helper3 CrossCarrierSchedulingConfig__schedulingCellInfo__helper4.
Opaque CrossCarrierSchedulingConfig__schedulingCellInfo__cond CrossCarrierSchedulingConfig__schedulingCellInfo__Format.

Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__Format : T_Format Z CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__cond :=
 ranged_int_format (0) (3) CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__helper1 CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__helper2.

Opaque CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__cond CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__Format.

Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__Format : T_Format Z CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__cond :=
 ranged_int_format (0) (3) CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__helper1 CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__helper2.

Opaque CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__cond CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__Format.


Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Format_Type := Eval cbn in seq_format_prod CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list.
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Format_list : CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Format_Type :=
  (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16__Format, (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16__Format, unit_format)).
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list__Format := (*Eval compute in *) seq_format CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Format_list.
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1 z :=
  (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_1_2_r16 z, (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__carrierIndicatorSizeDCI_0_2_r16 z, tt)).
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F2 (y : seq_type CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Type i0 i1
  end.
Lemma CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1F2_cond (z : CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Type)
  : CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond z ->
  (seq_cond CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1 z)).
intro H. unfold CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond in H. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1F2_cond2 (z : CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Type)
 : CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F2 (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F2F1_cond (y : seq_type CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list)
  : seq_cond CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list y ->
 (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F2 y)) /\  CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1 (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond. simpl in *. auto.
 - simpl. unfold CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Format : T_Format CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Type CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond :=
        proj2_format  CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__list__Format
    CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1 CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F2 CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1F2_cond  CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F1F2_cond2 CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__F2F1_cond.
Opaque CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__cond CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Format.

Definition CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Format : T_Format CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__nat__Format CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F1 CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F2 CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F1F2 CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__F2F1.

Opaque CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__cond CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Format.


Definition CrossCarrierSchedulingConfig__ext0O__Format_Type := Eval cbn in seq_format_prod CrossCarrierSchedulingConfig__ext0O__list.
Definition CrossCarrierSchedulingConfig__ext0O__Format_list : CrossCarrierSchedulingConfig__ext0O__Format_Type :=
  (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16__Format, (CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16__Format, unit_format)).
Definition CrossCarrierSchedulingConfig__ext0O__list__Format := (*Eval compute in *) seq_format CrossCarrierSchedulingConfig__ext0O__list CrossCarrierSchedulingConfig__ext0O__Format_list.
Definition CrossCarrierSchedulingConfig__ext0O__F1 z :=
  (CrossCarrierSchedulingConfig__ext0O__carrierIndicatorSize_r16 z, (CrossCarrierSchedulingConfig__ext0O__enableDefaultBeamForCCS_r16 z, tt)).
Definition CrossCarrierSchedulingConfig__ext0O__F2 (y : seq_type CrossCarrierSchedulingConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CrossCarrierSchedulingConfig__ext0O__Type i0 i1
  end.
Lemma CrossCarrierSchedulingConfig__ext0O__F1F2_cond (z : CrossCarrierSchedulingConfig__ext0O__Type)
  : CrossCarrierSchedulingConfig__ext0O__cond z ->
  (seq_cond CrossCarrierSchedulingConfig__ext0O__list (CrossCarrierSchedulingConfig__ext0O__F1 z)).
intro H. unfold CrossCarrierSchedulingConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__ext0O__F1F2_cond2 (z : CrossCarrierSchedulingConfig__ext0O__Type)
 : CrossCarrierSchedulingConfig__ext0O__F2 (CrossCarrierSchedulingConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__ext0O__F2F1_cond (y : seq_type CrossCarrierSchedulingConfig__ext0O__list)
  : seq_cond CrossCarrierSchedulingConfig__ext0O__list y ->
 (CrossCarrierSchedulingConfig__ext0O__cond (CrossCarrierSchedulingConfig__ext0O__F2 y)) /\  CrossCarrierSchedulingConfig__ext0O__F1 (CrossCarrierSchedulingConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CrossCarrierSchedulingConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold CrossCarrierSchedulingConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CrossCarrierSchedulingConfig__ext0O__Format : T_Format CrossCarrierSchedulingConfig__ext0O__Type CrossCarrierSchedulingConfig__ext0O__cond :=
        proj2_format  CrossCarrierSchedulingConfig__ext0O__cond CrossCarrierSchedulingConfig__ext0O__list__Format
    CrossCarrierSchedulingConfig__ext0O__F1 CrossCarrierSchedulingConfig__ext0O__F2 CrossCarrierSchedulingConfig__ext0O__F1F2_cond  CrossCarrierSchedulingConfig__ext0O__F1F2_cond2 CrossCarrierSchedulingConfig__ext0O__F2F1_cond.
Opaque CrossCarrierSchedulingConfig__ext0O__cond CrossCarrierSchedulingConfig__ext0O__Format.

Definition CrossCarrierSchedulingConfig__ext0__check_all_none (b : CrossCarrierSchedulingConfig__ext0O__Type) : bool :=
match b with 
  | make__CrossCarrierSchedulingConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition CrossCarrierSchedulingConfig__ext0__Format : T_Format CrossCarrierSchedulingConfig__ext0__Type CrossCarrierSchedulingConfig__ext0__cond :=
  restrict_add_format CrossCarrierSchedulingConfig__ext0__check_all_none CrossCarrierSchedulingConfig__ext0O__Format.

Opaque CrossCarrierSchedulingConfig__ext0__cond CrossCarrierSchedulingConfig__ext0__Format.

Definition CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Format : T_Format CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__nat__Format CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F1 CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F2 CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F1F2 CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__F2F1.

Opaque CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__cond CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Format.


Definition CrossCarrierSchedulingConfig__ext1O__Format_Type := Eval cbn in seq_format_prod CrossCarrierSchedulingConfig__ext1O__list.
Definition CrossCarrierSchedulingConfig__ext1O__Format_list : CrossCarrierSchedulingConfig__ext1O__Format_Type :=
  (CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17__Format, unit_format).
Definition CrossCarrierSchedulingConfig__ext1O__list__Format := (*Eval compute in *) seq_format CrossCarrierSchedulingConfig__ext1O__list CrossCarrierSchedulingConfig__ext1O__Format_list.
Definition CrossCarrierSchedulingConfig__ext1O__F1 z :=
  (CrossCarrierSchedulingConfig__ext1O__ccs_BlindDetectionSplit_r17 z, tt).
Definition CrossCarrierSchedulingConfig__ext1O__F2 (y : seq_type CrossCarrierSchedulingConfig__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__CrossCarrierSchedulingConfig__ext1O__Type i0
  end.
Lemma CrossCarrierSchedulingConfig__ext1O__F1F2_cond (z : CrossCarrierSchedulingConfig__ext1O__Type)
  : CrossCarrierSchedulingConfig__ext1O__cond z ->
  (seq_cond CrossCarrierSchedulingConfig__ext1O__list (CrossCarrierSchedulingConfig__ext1O__F1 z)).
intro H. unfold CrossCarrierSchedulingConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__ext1O__F1F2_cond2 (z : CrossCarrierSchedulingConfig__ext1O__Type)
 : CrossCarrierSchedulingConfig__ext1O__F2 (CrossCarrierSchedulingConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CrossCarrierSchedulingConfig__ext1O__F2F1_cond (y : seq_type CrossCarrierSchedulingConfig__ext1O__list)
  : seq_cond CrossCarrierSchedulingConfig__ext1O__list y ->
 (CrossCarrierSchedulingConfig__ext1O__cond (CrossCarrierSchedulingConfig__ext1O__F2 y)) /\  CrossCarrierSchedulingConfig__ext1O__F1 (CrossCarrierSchedulingConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CrossCarrierSchedulingConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold CrossCarrierSchedulingConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CrossCarrierSchedulingConfig__ext1O__Format : T_Format CrossCarrierSchedulingConfig__ext1O__Type CrossCarrierSchedulingConfig__ext1O__cond :=
        proj2_format  CrossCarrierSchedulingConfig__ext1O__cond CrossCarrierSchedulingConfig__ext1O__list__Format
    CrossCarrierSchedulingConfig__ext1O__F1 CrossCarrierSchedulingConfig__ext1O__F2 CrossCarrierSchedulingConfig__ext1O__F1F2_cond  CrossCarrierSchedulingConfig__ext1O__F1F2_cond2 CrossCarrierSchedulingConfig__ext1O__F2F1_cond.
Opaque CrossCarrierSchedulingConfig__ext1O__cond CrossCarrierSchedulingConfig__ext1O__Format.

Definition CrossCarrierSchedulingConfig__ext1__check_all_none (b : CrossCarrierSchedulingConfig__ext1O__Type) : bool :=
match b with 
  | make__CrossCarrierSchedulingConfig__ext1O__Type None  => false 
  | _ => true 
 end.
Definition CrossCarrierSchedulingConfig__ext1__Format : T_Format CrossCarrierSchedulingConfig__ext1__Type CrossCarrierSchedulingConfig__ext1__cond :=
  restrict_add_format CrossCarrierSchedulingConfig__ext1__check_all_none CrossCarrierSchedulingConfig__ext1O__Format.

Opaque CrossCarrierSchedulingConfig__ext1__cond CrossCarrierSchedulingConfig__ext1__Format.


Definition CrossCarrierSchedulingConfig__root_Format_Type := Eval cbn in seq_format_prod CrossCarrierSchedulingConfig__root_list.
Definition CrossCarrierSchedulingConfig__root_Format_list : CrossCarrierSchedulingConfig__root_Format_Type :=
  (CrossCarrierSchedulingConfig__schedulingCellInfo__Format, unit_format).

Definition CrossCarrierSchedulingConfig__ext_Format_Type := Eval cbn in get_formats CrossCarrierSchedulingConfig__ext_list.
Definition CrossCarrierSchedulingConfig__ext_Format_list : CrossCarrierSchedulingConfig__ext_Format_Type :=
  (CrossCarrierSchedulingConfig__ext0__Format, (CrossCarrierSchedulingConfig__ext1__Format, unit__Format)).

Definition CrossCarrierSchedulingConfig__list_type : Set := (seq_type CrossCarrierSchedulingConfig__root_list) * (seq_ext_type CrossCarrierSchedulingConfig__ext_list).
Definition CrossCarrierSchedulingConfig__list_cond (z : CrossCarrierSchedulingConfig__list_type) : Prop :=
        (seq_cond CrossCarrierSchedulingConfig__root_list (fst z)) /\ (seq_ext_cond CrossCarrierSchedulingConfig__ext_list (snd z)).
Definition CrossCarrierSchedulingConfig__list_format : T_Format CrossCarrierSchedulingConfig__list_type CrossCarrierSchedulingConfig__list_cond :=
 (* Eval compute in *) seq_ext_format CrossCarrierSchedulingConfig__root_list CrossCarrierSchedulingConfig__root_Format_list CrossCarrierSchedulingConfig__ext_list CrossCarrierSchedulingConfig__ext_Format_list.

Opaque CrossCarrierSchedulingConfig__list_format.
Definition CrossCarrierSchedulingConfig__F1 (z : CrossCarrierSchedulingConfig__Type) : CrossCarrierSchedulingConfig__list_type :=
  (((CrossCarrierSchedulingConfig__schedulingCellInfo z, tt)), (
(CrossCarrierSchedulingConfig__ext0 z, (CrossCarrierSchedulingConfig__ext1 z, tt)))).
Definition CrossCarrierSchedulingConfig__F2 (y : CrossCarrierSchedulingConfig__list_type) : CrossCarrierSchedulingConfig__Type :=
  match y with
  | ((j0, _), (i0, (i1, _)))=>
    make__CrossCarrierSchedulingConfig__Type j0 i0 i1
  end.
Definition CrossCarrierSchedulingConfig__helper1 : (forall a : CrossCarrierSchedulingConfig__Type, CrossCarrierSchedulingConfig__cond a -> CrossCarrierSchedulingConfig__list_cond (CrossCarrierSchedulingConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CrossCarrierSchedulingConfig__helper2 : (forall a : CrossCarrierSchedulingConfig__Type, CrossCarrierSchedulingConfig__F2 (CrossCarrierSchedulingConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CrossCarrierSchedulingConfig__helper3 : (forall b : CrossCarrierSchedulingConfig__list_type, CrossCarrierSchedulingConfig__list_cond b -> CrossCarrierSchedulingConfig__cond (CrossCarrierSchedulingConfig__F2 b) /\ CrossCarrierSchedulingConfig__F1 (CrossCarrierSchedulingConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CrossCarrierSchedulingConfig__cond, CrossCarrierSchedulingConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CrossCarrierSchedulingConfig__Format : T_Format CrossCarrierSchedulingConfig__Type CrossCarrierSchedulingConfig__cond :=
 proj2_format CrossCarrierSchedulingConfig__cond CrossCarrierSchedulingConfig__list_format  CrossCarrierSchedulingConfig__F1 CrossCarrierSchedulingConfig__F2 CrossCarrierSchedulingConfig__helper1 CrossCarrierSchedulingConfig__helper2 CrossCarrierSchedulingConfig__helper3.

Opaque CrossCarrierSchedulingConfig__cond CrossCarrierSchedulingConfig__Format.

