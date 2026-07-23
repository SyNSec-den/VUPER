Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_SwitchingTimeNR.

Opaque SRS_SwitchingTimeNR__cond SRS_SwitchingTimeNR__Format.

Definition BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__Type := list SRS_SwitchingTimeNR__Type.

Lemma BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__helper1 : (0 <= 1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__cond (z : BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__Type) :=  (1 <= Z.of_nat (length z) <= maxSimultaneousBands)%Z /\ (list_and SRS_SwitchingTimeNR__cond z) .

Record BandParameters_v1540__srs_CarrierSwitch__nr__Type : Set :=
  make__BandParameters_v1540__srs_CarrierSwitch__nr__Type {
    BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR : BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__Type ;
}.
Definition BandParameters_v1540__srs_CarrierSwitch__nr__list := (
 Nor BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__Type BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__cond ::
 nil).
Definition BandParameters_v1540__srs_CarrierSwitch__nr__cond z := 
  BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__cond (BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR z) /\
  True.

Require Import NR.SRS_SwitchingTimeEUTRA.

Opaque SRS_SwitchingTimeEUTRA__cond SRS_SwitchingTimeEUTRA__Format.

Definition BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__Type := list SRS_SwitchingTimeEUTRA__Type.

Lemma BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__helper1 : (0 <= 1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__cond (z : BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__Type) :=  (1 <= Z.of_nat (length z) <= maxSimultaneousBands)%Z /\ (list_and SRS_SwitchingTimeEUTRA__cond z) .

Record BandParameters_v1540__srs_CarrierSwitch__eutra__Type : Set :=
  make__BandParameters_v1540__srs_CarrierSwitch__eutra__Type {
    BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA : BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__Type ;
}.
Definition BandParameters_v1540__srs_CarrierSwitch__eutra__list := (
 Nor BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__Type BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__cond ::
 nil).
Definition BandParameters_v1540__srs_CarrierSwitch__eutra__cond z := 
  BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__cond (BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA z) /\
  True.


Inductive BandParameters_v1540__srs_CarrierSwitch__Type : Set :=
  | BandParameters_v1540__srs_CarrierSwitch__nr : BandParameters_v1540__srs_CarrierSwitch__nr__Type -> BandParameters_v1540__srs_CarrierSwitch__Type
  | BandParameters_v1540__srs_CarrierSwitch__eutra : BandParameters_v1540__srs_CarrierSwitch__eutra__Type -> BandParameters_v1540__srs_CarrierSwitch__Type
.
Definition BandParameters_v1540__srs_CarrierSwitch__list : list typ := (
typ_cons BandParameters_v1540__srs_CarrierSwitch__nr__Type BandParameters_v1540__srs_CarrierSwitch__nr__cond ::
typ_cons BandParameters_v1540__srs_CarrierSwitch__eutra__Type BandParameters_v1540__srs_CarrierSwitch__eutra__cond ::
 nil).
Definition BandParameters_v1540__srs_CarrierSwitch__cond (c : BandParameters_v1540__srs_CarrierSwitch__Type) := 
  match c with
  | BandParameters_v1540__srs_CarrierSwitch__nr t => BandParameters_v1540__srs_CarrierSwitch__nr__cond t 
  | BandParameters_v1540__srs_CarrierSwitch__eutra t => BandParameters_v1540__srs_CarrierSwitch__eutra__cond t 
  end.

Lemma BandParameters_v1540__srs_CarrierSwitch__len_helper1 : to_bit_sz (length BandParameters_v1540__srs_CarrierSwitch__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandParameters_v1540__srs_CarrierSwitch__len_helper2 : 2 <= length2 BandParameters_v1540__srs_CarrierSwitch__list.
 simpl. lia. Qed.
Inductive BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Type : Set :=
 | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r2
 | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r4
 | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t2r4
 | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r4_t2r4
 | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r1
 | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t2r2
 | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t4r4
 | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__notSupported
.
Definition BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__cond := (fun (_ : BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Type) => True).
Lemma BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__nat__helper.

Definition BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F1 t :=
  match t with
  | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r2 => 0
  | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r4 => 1
  | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t2r4 => 2
  | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r4_t2r4 => 3
  | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r1 => 4
  | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t2r2 => 5
  | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t4r4 => 6
  | BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__notSupported => 7
  end.
Definition BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F2 n :=
  match n with
  | 0 => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r2
  | 1 => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r4
  | 2 => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t2r4
  | 3 => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r4_t2r4
  | 4 => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r1
  | 5 => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t2r2
  | 6 => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t4r4
  | 7 => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__notSupported
  | _ => BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__t1r2
  end.
Lemma BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F1F2 : forall x : BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Type, (BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F1 x <= 7) /\ BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F2 (BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F1 x) = x. imp_solve. Qed.
Lemma BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F2F1 : forall (y : nat) (H : y <= 7), BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F1 (BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F2 y) = y. enum_solve H y. Qed.

Lemma BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__Type := Z.
Definition BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__cond := (fun z => (1 <= z <= 32)%Z).
Lemma BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__Type := Z.
Definition BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__cond := (fun z => (1 <= z <= 32)%Z).
Record BandParameters_v1540__srs_TxSwitch__Type : Set :=
  make__BandParameters_v1540__srs_TxSwitch__Type {
    BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch : BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Type ;
    BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx : option Z ;
    BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand : option Z ;
}.
Definition BandParameters_v1540__srs_TxSwitch__list := (
 Nor BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Type BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__cond ::
 Opt Z BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__cond ::
 Opt Z BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__cond ::
 nil).
Definition BandParameters_v1540__srs_TxSwitch__cond z := 
  BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__cond (BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch z) /\
  opt_cond BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__cond (BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx z) /\
  opt_cond BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__cond (BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand z) /\
  True.

Record BandParameters_v1540__Type : Set :=
  make__BandParameters_v1540__Type {
    BandParameters_v1540__srs_CarrierSwitch : option BandParameters_v1540__srs_CarrierSwitch__Type ;
    BandParameters_v1540__srs_TxSwitch : option BandParameters_v1540__srs_TxSwitch__Type ;
}.
Definition BandParameters_v1540__list := (
 Opt BandParameters_v1540__srs_CarrierSwitch__Type BandParameters_v1540__srs_CarrierSwitch__cond ::
 Opt BandParameters_v1540__srs_TxSwitch__Type BandParameters_v1540__srs_TxSwitch__cond ::
 nil).
Definition BandParameters_v1540__cond z := 
  opt_cond BandParameters_v1540__srs_CarrierSwitch__cond (BandParameters_v1540__srs_CarrierSwitch z) /\
  opt_cond BandParameters_v1540__srs_TxSwitch__cond (BandParameters_v1540__srs_TxSwitch z) /\
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
Definition BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__Format : T_Format BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__Type BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__cond := seq_of_format SRS_SwitchingTimeNR__Format 1 maxSimultaneousBands BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__helper1 BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__helper2.

Opaque BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__cond BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__Format.


Definition BandParameters_v1540__srs_CarrierSwitch__nr__Format_Type := Eval cbn in seq_format_prod BandParameters_v1540__srs_CarrierSwitch__nr__list.
Definition BandParameters_v1540__srs_CarrierSwitch__nr__Format_list : BandParameters_v1540__srs_CarrierSwitch__nr__Format_Type :=
  (BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR__Format, unit_format).
Definition BandParameters_v1540__srs_CarrierSwitch__nr__list__Format := (*Eval compute in *) seq_format BandParameters_v1540__srs_CarrierSwitch__nr__list BandParameters_v1540__srs_CarrierSwitch__nr__Format_list.
Definition BandParameters_v1540__srs_CarrierSwitch__nr__F1 z :=
  (BandParameters_v1540__srs_CarrierSwitch__nr__srs_SwitchingTimesListNR z, tt).
Definition BandParameters_v1540__srs_CarrierSwitch__nr__F2 (y : seq_type BandParameters_v1540__srs_CarrierSwitch__nr__list) :=
  match y with
  | (i0, _)=>
    make__BandParameters_v1540__srs_CarrierSwitch__nr__Type i0
  end.
Lemma BandParameters_v1540__srs_CarrierSwitch__nr__F1F2_cond (z : BandParameters_v1540__srs_CarrierSwitch__nr__Type)
  : BandParameters_v1540__srs_CarrierSwitch__nr__cond z ->
  (seq_cond BandParameters_v1540__srs_CarrierSwitch__nr__list (BandParameters_v1540__srs_CarrierSwitch__nr__F1 z)).
intro H. unfold BandParameters_v1540__srs_CarrierSwitch__nr__cond in H. simpl. auto. Qed.
Lemma BandParameters_v1540__srs_CarrierSwitch__nr__F1F2_cond2 (z : BandParameters_v1540__srs_CarrierSwitch__nr__Type)
 : BandParameters_v1540__srs_CarrierSwitch__nr__F2 (BandParameters_v1540__srs_CarrierSwitch__nr__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters_v1540__srs_CarrierSwitch__nr__F2F1_cond (y : seq_type BandParameters_v1540__srs_CarrierSwitch__nr__list)
  : seq_cond BandParameters_v1540__srs_CarrierSwitch__nr__list y ->
 (BandParameters_v1540__srs_CarrierSwitch__nr__cond (BandParameters_v1540__srs_CarrierSwitch__nr__F2 y)) /\  BandParameters_v1540__srs_CarrierSwitch__nr__F1 (BandParameters_v1540__srs_CarrierSwitch__nr__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters_v1540__srs_CarrierSwitch__nr__cond. simpl in *. auto.
 - simpl. unfold BandParameters_v1540__srs_CarrierSwitch__nr__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters_v1540__srs_CarrierSwitch__nr__Format : T_Format BandParameters_v1540__srs_CarrierSwitch__nr__Type BandParameters_v1540__srs_CarrierSwitch__nr__cond :=
        proj2_format  BandParameters_v1540__srs_CarrierSwitch__nr__cond BandParameters_v1540__srs_CarrierSwitch__nr__list__Format
    BandParameters_v1540__srs_CarrierSwitch__nr__F1 BandParameters_v1540__srs_CarrierSwitch__nr__F2 BandParameters_v1540__srs_CarrierSwitch__nr__F1F2_cond  BandParameters_v1540__srs_CarrierSwitch__nr__F1F2_cond2 BandParameters_v1540__srs_CarrierSwitch__nr__F2F1_cond.
Opaque BandParameters_v1540__srs_CarrierSwitch__nr__cond BandParameters_v1540__srs_CarrierSwitch__nr__Format.

Definition BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__Format : T_Format BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__Type BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__cond := seq_of_format SRS_SwitchingTimeEUTRA__Format 1 maxSimultaneousBands BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__helper1 BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__helper2.

Opaque BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__cond BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__Format.


Definition BandParameters_v1540__srs_CarrierSwitch__eutra__Format_Type := Eval cbn in seq_format_prod BandParameters_v1540__srs_CarrierSwitch__eutra__list.
Definition BandParameters_v1540__srs_CarrierSwitch__eutra__Format_list : BandParameters_v1540__srs_CarrierSwitch__eutra__Format_Type :=
  (BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA__Format, unit_format).
Definition BandParameters_v1540__srs_CarrierSwitch__eutra__list__Format := (*Eval compute in *) seq_format BandParameters_v1540__srs_CarrierSwitch__eutra__list BandParameters_v1540__srs_CarrierSwitch__eutra__Format_list.
Definition BandParameters_v1540__srs_CarrierSwitch__eutra__F1 z :=
  (BandParameters_v1540__srs_CarrierSwitch__eutra__srs_SwitchingTimesListEUTRA z, tt).
Definition BandParameters_v1540__srs_CarrierSwitch__eutra__F2 (y : seq_type BandParameters_v1540__srs_CarrierSwitch__eutra__list) :=
  match y with
  | (i0, _)=>
    make__BandParameters_v1540__srs_CarrierSwitch__eutra__Type i0
  end.
Lemma BandParameters_v1540__srs_CarrierSwitch__eutra__F1F2_cond (z : BandParameters_v1540__srs_CarrierSwitch__eutra__Type)
  : BandParameters_v1540__srs_CarrierSwitch__eutra__cond z ->
  (seq_cond BandParameters_v1540__srs_CarrierSwitch__eutra__list (BandParameters_v1540__srs_CarrierSwitch__eutra__F1 z)).
intro H. unfold BandParameters_v1540__srs_CarrierSwitch__eutra__cond in H. simpl. auto. Qed.
Lemma BandParameters_v1540__srs_CarrierSwitch__eutra__F1F2_cond2 (z : BandParameters_v1540__srs_CarrierSwitch__eutra__Type)
 : BandParameters_v1540__srs_CarrierSwitch__eutra__F2 (BandParameters_v1540__srs_CarrierSwitch__eutra__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters_v1540__srs_CarrierSwitch__eutra__F2F1_cond (y : seq_type BandParameters_v1540__srs_CarrierSwitch__eutra__list)
  : seq_cond BandParameters_v1540__srs_CarrierSwitch__eutra__list y ->
 (BandParameters_v1540__srs_CarrierSwitch__eutra__cond (BandParameters_v1540__srs_CarrierSwitch__eutra__F2 y)) /\  BandParameters_v1540__srs_CarrierSwitch__eutra__F1 (BandParameters_v1540__srs_CarrierSwitch__eutra__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters_v1540__srs_CarrierSwitch__eutra__cond. simpl in *. auto.
 - simpl. unfold BandParameters_v1540__srs_CarrierSwitch__eutra__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters_v1540__srs_CarrierSwitch__eutra__Format : T_Format BandParameters_v1540__srs_CarrierSwitch__eutra__Type BandParameters_v1540__srs_CarrierSwitch__eutra__cond :=
        proj2_format  BandParameters_v1540__srs_CarrierSwitch__eutra__cond BandParameters_v1540__srs_CarrierSwitch__eutra__list__Format
    BandParameters_v1540__srs_CarrierSwitch__eutra__F1 BandParameters_v1540__srs_CarrierSwitch__eutra__F2 BandParameters_v1540__srs_CarrierSwitch__eutra__F1F2_cond  BandParameters_v1540__srs_CarrierSwitch__eutra__F1F2_cond2 BandParameters_v1540__srs_CarrierSwitch__eutra__F2F1_cond.
Opaque BandParameters_v1540__srs_CarrierSwitch__eutra__cond BandParameters_v1540__srs_CarrierSwitch__eutra__Format.


Definition BandParameters_v1540__srs_CarrierSwitch__Format_Type := Eval cbn in get_formats BandParameters_v1540__srs_CarrierSwitch__list.
Definition BandParameters_v1540__srs_CarrierSwitch__Format_list : BandParameters_v1540__srs_CarrierSwitch__Format_Type :=
  (BandParameters_v1540__srs_CarrierSwitch__nr__Format, (BandParameters_v1540__srs_CarrierSwitch__eutra__Format, unit__Format)).
Definition BandParameters_v1540__srs_CarrierSwitch__list__Format := Eval compute in choice_format BandParameters_v1540__srs_CarrierSwitch__list BandParameters_v1540__srs_CarrierSwitch__len_helper1 BandParameters_v1540__srs_CarrierSwitch__len_helper2  BandParameters_v1540__srs_CarrierSwitch__Format_list.
Definition BandParameters_v1540__srs_CarrierSwitch__F1 (z : BandParameters_v1540__srs_CarrierSwitch__Type) : (choice BandParameters_v1540__srs_CarrierSwitch__list) :=
  match z with
   | BandParameters_v1540__srs_CarrierSwitch__nr t => existT _ 0 t
  | BandParameters_v1540__srs_CarrierSwitch__eutra t => existT _ 1 t
  end.
Definition BandParameters_v1540__srs_CarrierSwitch__g := (fun n => typ_set (get_nth_typ BandParameters_v1540__srs_CarrierSwitch__list n)).
Definition BandParameters_v1540__srs_CarrierSwitch__F2 (y : choice BandParameters_v1540__srs_CarrierSwitch__list) : BandParameters_v1540__srs_CarrierSwitch__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandParameters_v1540__srs_CarrierSwitch__g n -> BandParameters_v1540__srs_CarrierSwitch__Type) with
    | 0 => fun (t : BandParameters_v1540__srs_CarrierSwitch__nr__Type) => BandParameters_v1540__srs_CarrierSwitch__nr t 
    | 1 => fun (t : BandParameters_v1540__srs_CarrierSwitch__eutra__Type) => BandParameters_v1540__srs_CarrierSwitch__eutra t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandParameters_v1540__srs_CarrierSwitch__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandParameters_v1540__srs_CarrierSwitch__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandParameters_v1540__srs_CarrierSwitch__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandParameters_v1540__srs_CarrierSwitch__Type with end) n0
           end t0).

Lemma BandParameters_v1540__srs_CarrierSwitch__helper2 :  forall (y : BandParameters_v1540__srs_CarrierSwitch__Type), BandParameters_v1540__srs_CarrierSwitch__cond y -> choice_cond BandParameters_v1540__srs_CarrierSwitch__list (BandParameters_v1540__srs_CarrierSwitch__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandParameters_v1540__srs_CarrierSwitch__helper3 :  forall (y : BandParameters_v1540__srs_CarrierSwitch__Type), BandParameters_v1540__srs_CarrierSwitch__F2 (BandParameters_v1540__srs_CarrierSwitch__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandParameters_v1540__srs_CarrierSwitch__helper4 : (forall b : choice BandParameters_v1540__srs_CarrierSwitch__list, choice_cond BandParameters_v1540__srs_CarrierSwitch__list b -> BandParameters_v1540__srs_CarrierSwitch__cond (BandParameters_v1540__srs_CarrierSwitch__F2 b) /\ BandParameters_v1540__srs_CarrierSwitch__F1 (BandParameters_v1540__srs_CarrierSwitch__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandParameters_v1540__srs_CarrierSwitch__F1 BandParameters_v1540__srs_CarrierSwitch__F2.
Definition BandParameters_v1540__srs_CarrierSwitch__Format : T_Format BandParameters_v1540__srs_CarrierSwitch__Type BandParameters_v1540__srs_CarrierSwitch__cond :=
  (* Eval compute in *) proj2_format BandParameters_v1540__srs_CarrierSwitch__cond BandParameters_v1540__srs_CarrierSwitch__list__Format BandParameters_v1540__srs_CarrierSwitch__F1 BandParameters_v1540__srs_CarrierSwitch__F2 BandParameters_v1540__srs_CarrierSwitch__helper2 BandParameters_v1540__srs_CarrierSwitch__helper3 BandParameters_v1540__srs_CarrierSwitch__helper4.
Opaque BandParameters_v1540__srs_CarrierSwitch__cond BandParameters_v1540__srs_CarrierSwitch__Format.

Definition BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Format : T_Format BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__nat__Format BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F1 BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F2 BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F1F2 BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__F2F1.

Opaque BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__cond BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Format.

Definition BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__Format : T_Format Z BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__cond :=
 ranged_int_format (1) (32) BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__helper1 BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__helper2.

Opaque BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__cond BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__Format.

Definition BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__Format : T_Format Z BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__cond :=
 ranged_int_format (1) (32) BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__helper1 BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__helper2.

Opaque BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__cond BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__Format.


Definition BandParameters_v1540__srs_TxSwitch__Format_Type := Eval cbn in seq_format_prod BandParameters_v1540__srs_TxSwitch__list.
Definition BandParameters_v1540__srs_TxSwitch__Format_list : BandParameters_v1540__srs_TxSwitch__Format_Type :=
  (BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch__Format, (BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx__Format, (BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand__Format, unit_format))).
Definition BandParameters_v1540__srs_TxSwitch__list__Format := (*Eval compute in *) seq_format BandParameters_v1540__srs_TxSwitch__list BandParameters_v1540__srs_TxSwitch__Format_list.
Definition BandParameters_v1540__srs_TxSwitch__F1 z :=
  (BandParameters_v1540__srs_TxSwitch__supportedSRS_TxPortSwitch z, (BandParameters_v1540__srs_TxSwitch__txSwitchImpactToRx z, (BandParameters_v1540__srs_TxSwitch__txSwitchWithAnotherBand z, tt))).
Definition BandParameters_v1540__srs_TxSwitch__F2 (y : seq_type BandParameters_v1540__srs_TxSwitch__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandParameters_v1540__srs_TxSwitch__Type i0 i1 i2
  end.
Lemma BandParameters_v1540__srs_TxSwitch__F1F2_cond (z : BandParameters_v1540__srs_TxSwitch__Type)
  : BandParameters_v1540__srs_TxSwitch__cond z ->
  (seq_cond BandParameters_v1540__srs_TxSwitch__list (BandParameters_v1540__srs_TxSwitch__F1 z)).
intro H. unfold BandParameters_v1540__srs_TxSwitch__cond in H. simpl. auto. Qed.
Lemma BandParameters_v1540__srs_TxSwitch__F1F2_cond2 (z : BandParameters_v1540__srs_TxSwitch__Type)
 : BandParameters_v1540__srs_TxSwitch__F2 (BandParameters_v1540__srs_TxSwitch__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters_v1540__srs_TxSwitch__F2F1_cond (y : seq_type BandParameters_v1540__srs_TxSwitch__list)
  : seq_cond BandParameters_v1540__srs_TxSwitch__list y ->
 (BandParameters_v1540__srs_TxSwitch__cond (BandParameters_v1540__srs_TxSwitch__F2 y)) /\  BandParameters_v1540__srs_TxSwitch__F1 (BandParameters_v1540__srs_TxSwitch__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters_v1540__srs_TxSwitch__cond. simpl in *. auto.
 - simpl. unfold BandParameters_v1540__srs_TxSwitch__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters_v1540__srs_TxSwitch__Format : T_Format BandParameters_v1540__srs_TxSwitch__Type BandParameters_v1540__srs_TxSwitch__cond :=
        proj2_format  BandParameters_v1540__srs_TxSwitch__cond BandParameters_v1540__srs_TxSwitch__list__Format
    BandParameters_v1540__srs_TxSwitch__F1 BandParameters_v1540__srs_TxSwitch__F2 BandParameters_v1540__srs_TxSwitch__F1F2_cond  BandParameters_v1540__srs_TxSwitch__F1F2_cond2 BandParameters_v1540__srs_TxSwitch__F2F1_cond.
Opaque BandParameters_v1540__srs_TxSwitch__cond BandParameters_v1540__srs_TxSwitch__Format.


Definition BandParameters_v1540__Format_Type := Eval cbn in seq_format_prod BandParameters_v1540__list.
Definition BandParameters_v1540__Format_list : BandParameters_v1540__Format_Type :=
  (BandParameters_v1540__srs_CarrierSwitch__Format, (BandParameters_v1540__srs_TxSwitch__Format, unit_format)).
Definition BandParameters_v1540__list__Format := (*Eval compute in *) seq_format BandParameters_v1540__list BandParameters_v1540__Format_list.
Definition BandParameters_v1540__F1 z :=
  (BandParameters_v1540__srs_CarrierSwitch z, (BandParameters_v1540__srs_TxSwitch z, tt)).
Definition BandParameters_v1540__F2 (y : seq_type BandParameters_v1540__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandParameters_v1540__Type i0 i1
  end.
Lemma BandParameters_v1540__F1F2_cond (z : BandParameters_v1540__Type)
  : BandParameters_v1540__cond z ->
  (seq_cond BandParameters_v1540__list (BandParameters_v1540__F1 z)).
intro H. unfold BandParameters_v1540__cond in H. simpl. auto. Qed.
Lemma BandParameters_v1540__F1F2_cond2 (z : BandParameters_v1540__Type)
 : BandParameters_v1540__F2 (BandParameters_v1540__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters_v1540__F2F1_cond (y : seq_type BandParameters_v1540__list)
  : seq_cond BandParameters_v1540__list y ->
 (BandParameters_v1540__cond (BandParameters_v1540__F2 y)) /\  BandParameters_v1540__F1 (BandParameters_v1540__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters_v1540__cond. simpl in *. auto.
 - simpl. unfold BandParameters_v1540__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters_v1540__Format : T_Format BandParameters_v1540__Type BandParameters_v1540__cond :=
        proj2_format  BandParameters_v1540__cond BandParameters_v1540__list__Format
    BandParameters_v1540__F1 BandParameters_v1540__F2 BandParameters_v1540__F1F2_cond  BandParameters_v1540__F1F2_cond2 BandParameters_v1540__F2F1_cond.
Opaque BandParameters_v1540__cond BandParameters_v1540__Format.

