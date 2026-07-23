Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandParameters.

Opaque BandParameters__cond BandParameters__Format.

Definition BandCombination__bandList__Type := list BandParameters__Type.

Lemma BandCombination__bandList__helper1 : (0 <= 1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma BandCombination__bandList__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombination__bandList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombination__bandList__cond (z : BandCombination__bandList__Type) :=  (1 <= Z.of_nat (length z) <= maxSimultaneousBands)%Z /\ (list_and BandParameters__cond z) .

Require Import NR.FeatureSetCombinationId.

Opaque FeatureSetCombinationId__cond FeatureSetCombinationId__Format.

Require Import NR.CA_ParametersEUTRA.

Opaque CA_ParametersEUTRA__cond CA_ParametersEUTRA__Format.

Require Import NR.CA_ParametersNR.

Opaque CA_ParametersNR__cond CA_ParametersNR__Format.

Require Import NR.MRDC_Parameters.

Opaque MRDC_Parameters__cond MRDC_Parameters__Format.

Lemma BandCombination__supportedBandwidthCombinationSet__helper1 : (0 <= 1 <= 32)%Z.  lia. Qed.
Lemma BandCombination__supportedBandwidthCombinationSet__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombination__supportedBandwidthCombinationSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombination__supportedBandwidthCombinationSet__Type := bit_string.
Definition BandCombination__supportedBandwidthCombinationSet__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 32)%Z /\ bit_string_len_prop (fst z) (snd z)).
Inductive BandCombination__powerClass_v1530__Type : Set :=
 | BandCombination__powerClass_v1530__pc2
.
Definition BandCombination__powerClass_v1530__cond := (fun (_ : BandCombination__powerClass_v1530__Type) => True).
Lemma BandCombination__powerClass_v1530__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandCombination__powerClass_v1530__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandCombination__powerClass_v1530__nat__helper.

Definition BandCombination__powerClass_v1530__F1 t :=
  match t with
  | BandCombination__powerClass_v1530__pc2 => 0
  end.
Definition BandCombination__powerClass_v1530__F2 n :=
  match n with
  | 0 => BandCombination__powerClass_v1530__pc2
  | _ => BandCombination__powerClass_v1530__pc2
  end.
Lemma BandCombination__powerClass_v1530__F1F2 : forall x : BandCombination__powerClass_v1530__Type, (BandCombination__powerClass_v1530__F1 x <= 0) /\ BandCombination__powerClass_v1530__F2 (BandCombination__powerClass_v1530__F1 x) = x. imp_solve. Qed.
Lemma BandCombination__powerClass_v1530__F2F1 : forall (y : nat) (H : y <= 0), BandCombination__powerClass_v1530__F1 (BandCombination__powerClass_v1530__F2 y) = y. enum_solve H y. Qed.

Record BandCombination__Type : Set :=
  make__BandCombination__Type {
    BandCombination__bandList : BandCombination__bandList__Type ;
    BandCombination__featureSetCombination : FeatureSetCombinationId__Type ;
    BandCombination__ca_ParametersEUTRA : option CA_ParametersEUTRA__Type ;
    BandCombination__ca_ParametersNR : option CA_ParametersNR__Type ;
    BandCombination__mrdc_Parameters : option MRDC_Parameters__Type ;
    BandCombination__supportedBandwidthCombinationSet : option BandCombination__supportedBandwidthCombinationSet__Type ;
    BandCombination__powerClass_v1530 : option BandCombination__powerClass_v1530__Type ;
}.
Definition BandCombination__list := (
 Nor BandCombination__bandList__Type BandCombination__bandList__cond ::
 Nor FeatureSetCombinationId__Type FeatureSetCombinationId__cond ::
 Opt CA_ParametersEUTRA__Type CA_ParametersEUTRA__cond ::
 Opt CA_ParametersNR__Type CA_ParametersNR__cond ::
 Opt MRDC_Parameters__Type MRDC_Parameters__cond ::
 Opt BandCombination__supportedBandwidthCombinationSet__Type BandCombination__supportedBandwidthCombinationSet__cond ::
 Opt BandCombination__powerClass_v1530__Type BandCombination__powerClass_v1530__cond ::
 nil).
Definition BandCombination__cond z := 
  BandCombination__bandList__cond (BandCombination__bandList z) /\
  FeatureSetCombinationId__cond (BandCombination__featureSetCombination z) /\
  opt_cond CA_ParametersEUTRA__cond (BandCombination__ca_ParametersEUTRA z) /\
  opt_cond CA_ParametersNR__cond (BandCombination__ca_ParametersNR z) /\
  opt_cond MRDC_Parameters__cond (BandCombination__mrdc_Parameters z) /\
  opt_cond BandCombination__supportedBandwidthCombinationSet__cond (BandCombination__supportedBandwidthCombinationSet z) /\
  opt_cond BandCombination__powerClass_v1530__cond (BandCombination__powerClass_v1530 z) /\
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
Definition BandCombination__bandList__Format : T_Format BandCombination__bandList__Type BandCombination__bandList__cond := seq_of_format BandParameters__Format 1 maxSimultaneousBands BandCombination__bandList__helper1 BandCombination__bandList__helper2.

Opaque BandCombination__bandList__cond BandCombination__bandList__Format.

Definition BandCombination__supportedBandwidthCombinationSet__Format : T_Format BandCombination__supportedBandwidthCombinationSet__Type BandCombination__supportedBandwidthCombinationSet__cond := (* Eval compute in *) bit_string_ranged_format 1 32 BandCombination__supportedBandwidthCombinationSet__helper1 BandCombination__supportedBandwidthCombinationSet__helper2.
Opaque BandCombination__supportedBandwidthCombinationSet__cond BandCombination__supportedBandwidthCombinationSet__Format.

Definition BandCombination__powerClass_v1530__Format : T_Format BandCombination__powerClass_v1530__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandCombination__powerClass_v1530__nat__Format BandCombination__powerClass_v1530__F1 BandCombination__powerClass_v1530__F2 BandCombination__powerClass_v1530__F1F2 BandCombination__powerClass_v1530__F2F1.

Opaque BandCombination__powerClass_v1530__cond BandCombination__powerClass_v1530__Format.


Definition BandCombination__Format_Type := Eval cbn in seq_format_prod BandCombination__list.
Definition BandCombination__Format_list : BandCombination__Format_Type :=
  (BandCombination__bandList__Format, (FeatureSetCombinationId__Format, (CA_ParametersEUTRA__Format, (CA_ParametersNR__Format, (MRDC_Parameters__Format, (BandCombination__supportedBandwidthCombinationSet__Format, (BandCombination__powerClass_v1530__Format, unit_format))))))).
Definition BandCombination__list__Format := (*Eval compute in *) seq_format BandCombination__list BandCombination__Format_list.
Definition BandCombination__F1 z :=
  (BandCombination__bandList z, (BandCombination__featureSetCombination z, (BandCombination__ca_ParametersEUTRA z, (BandCombination__ca_ParametersNR z, (BandCombination__mrdc_Parameters z, (BandCombination__supportedBandwidthCombinationSet z, (BandCombination__powerClass_v1530 z, tt))))))).
Definition BandCombination__F2 (y : seq_type BandCombination__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__BandCombination__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma BandCombination__F1F2_cond (z : BandCombination__Type)
  : BandCombination__cond z ->
  (seq_cond BandCombination__list (BandCombination__F1 z)).
intro H. unfold BandCombination__cond in H. simpl. auto. Qed.
Lemma BandCombination__F1F2_cond2 (z : BandCombination__Type)
 : BandCombination__F2 (BandCombination__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombination__F2F1_cond (y : seq_type BandCombination__list)
  : seq_cond BandCombination__list y ->
 (BandCombination__cond (BandCombination__F2 y)) /\  BandCombination__F1 (BandCombination__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombination__cond. simpl in *. auto.
 - simpl. unfold BandCombination__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombination__Format : T_Format BandCombination__Type BandCombination__cond :=
        proj2_format  BandCombination__cond BandCombination__list__Format
    BandCombination__F1 BandCombination__F2 BandCombination__F1F2_cond  BandCombination__F1F2_cond2 BandCombination__F2F1_cond.
Opaque BandCombination__cond BandCombination__Format.

