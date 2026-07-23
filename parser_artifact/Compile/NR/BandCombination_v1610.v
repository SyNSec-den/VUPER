Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandParameters_v1610.

Opaque BandParameters_v1610__cond BandParameters_v1610__Format.

Definition BandCombination_v1610__bandList_v1610__Type := list BandParameters_v1610__Type.

Lemma BandCombination_v1610__bandList_v1610__helper1 : (0 <= 1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma BandCombination_v1610__bandList_v1610__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombination_v1610__bandList_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombination_v1610__bandList_v1610__cond (z : BandCombination_v1610__bandList_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxSimultaneousBands)%Z /\ (list_and BandParameters_v1610__cond z) .

Require Import NR.CA_ParametersNR_v1610.

Opaque CA_ParametersNR_v1610__cond CA_ParametersNR_v1610__Format.

Require Import NR.CA_ParametersNRDC_v1610.

Opaque CA_ParametersNRDC_v1610__cond CA_ParametersNRDC_v1610__Format.

Inductive BandCombination_v1610__powerClass_v1610__Type : Set :=
 | BandCombination_v1610__powerClass_v1610__pc1dot5
.
Definition BandCombination_v1610__powerClass_v1610__cond := (fun (_ : BandCombination_v1610__powerClass_v1610__Type) => True).
Lemma BandCombination_v1610__powerClass_v1610__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandCombination_v1610__powerClass_v1610__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandCombination_v1610__powerClass_v1610__nat__helper.

Definition BandCombination_v1610__powerClass_v1610__F1 t :=
  match t with
  | BandCombination_v1610__powerClass_v1610__pc1dot5 => 0
  end.
Definition BandCombination_v1610__powerClass_v1610__F2 n :=
  match n with
  | 0 => BandCombination_v1610__powerClass_v1610__pc1dot5
  | _ => BandCombination_v1610__powerClass_v1610__pc1dot5
  end.
Lemma BandCombination_v1610__powerClass_v1610__F1F2 : forall x : BandCombination_v1610__powerClass_v1610__Type, (BandCombination_v1610__powerClass_v1610__F1 x <= 0) /\ BandCombination_v1610__powerClass_v1610__F2 (BandCombination_v1610__powerClass_v1610__F1 x) = x. imp_solve. Qed.
Lemma BandCombination_v1610__powerClass_v1610__F2F1 : forall (y : nat) (H : y <= 0), BandCombination_v1610__powerClass_v1610__F1 (BandCombination_v1610__powerClass_v1610__F2 y) = y. enum_solve H y. Qed.

Inductive BandCombination_v1610__powerClassNRPart_r16__Type : Set :=
 | BandCombination_v1610__powerClassNRPart_r16__pc1
 | BandCombination_v1610__powerClassNRPart_r16__pc2
 | BandCombination_v1610__powerClassNRPart_r16__pc3
 | BandCombination_v1610__powerClassNRPart_r16__pc5
.
Definition BandCombination_v1610__powerClassNRPart_r16__cond := (fun (_ : BandCombination_v1610__powerClassNRPart_r16__Type) => True).
Lemma BandCombination_v1610__powerClassNRPart_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandCombination_v1610__powerClassNRPart_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BandCombination_v1610__powerClassNRPart_r16__nat__helper.

Definition BandCombination_v1610__powerClassNRPart_r16__F1 t :=
  match t with
  | BandCombination_v1610__powerClassNRPart_r16__pc1 => 0
  | BandCombination_v1610__powerClassNRPart_r16__pc2 => 1
  | BandCombination_v1610__powerClassNRPart_r16__pc3 => 2
  | BandCombination_v1610__powerClassNRPart_r16__pc5 => 3
  end.
Definition BandCombination_v1610__powerClassNRPart_r16__F2 n :=
  match n with
  | 0 => BandCombination_v1610__powerClassNRPart_r16__pc1
  | 1 => BandCombination_v1610__powerClassNRPart_r16__pc2
  | 2 => BandCombination_v1610__powerClassNRPart_r16__pc3
  | 3 => BandCombination_v1610__powerClassNRPart_r16__pc5
  | _ => BandCombination_v1610__powerClassNRPart_r16__pc1
  end.
Lemma BandCombination_v1610__powerClassNRPart_r16__F1F2 : forall x : BandCombination_v1610__powerClassNRPart_r16__Type, (BandCombination_v1610__powerClassNRPart_r16__F1 x <= 3) /\ BandCombination_v1610__powerClassNRPart_r16__F2 (BandCombination_v1610__powerClassNRPart_r16__F1 x) = x. imp_solve. Qed.
Lemma BandCombination_v1610__powerClassNRPart_r16__F2F1 : forall (y : nat) (H : y <= 3), BandCombination_v1610__powerClassNRPart_r16__F1 (BandCombination_v1610__powerClassNRPart_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.FeatureSetCombinationId.

Opaque FeatureSetCombinationId__cond FeatureSetCombinationId__Format.

Require Import NR.MRDC_Parameters_v1620.

Opaque MRDC_Parameters_v1620__cond MRDC_Parameters_v1620__Format.

Record BandCombination_v1610__Type : Set :=
  make__BandCombination_v1610__Type {
    BandCombination_v1610__bandList_v1610 : option BandCombination_v1610__bandList_v1610__Type ;
    BandCombination_v1610__ca_ParametersNR_v1610 : option CA_ParametersNR_v1610__Type ;
    BandCombination_v1610__ca_ParametersNRDC_v1610 : option CA_ParametersNRDC_v1610__Type ;
    BandCombination_v1610__powerClass_v1610 : option BandCombination_v1610__powerClass_v1610__Type ;
    BandCombination_v1610__powerClassNRPart_r16 : option BandCombination_v1610__powerClassNRPart_r16__Type ;
    BandCombination_v1610__featureSetCombinationDAPS_r16 : option FeatureSetCombinationId__Type ;
    BandCombination_v1610__mrdc_Parameters_v1620 : option MRDC_Parameters_v1620__Type ;
}.
Definition BandCombination_v1610__list := (
 Opt BandCombination_v1610__bandList_v1610__Type BandCombination_v1610__bandList_v1610__cond ::
 Opt CA_ParametersNR_v1610__Type CA_ParametersNR_v1610__cond ::
 Opt CA_ParametersNRDC_v1610__Type CA_ParametersNRDC_v1610__cond ::
 Opt BandCombination_v1610__powerClass_v1610__Type BandCombination_v1610__powerClass_v1610__cond ::
 Opt BandCombination_v1610__powerClassNRPart_r16__Type BandCombination_v1610__powerClassNRPart_r16__cond ::
 Opt FeatureSetCombinationId__Type FeatureSetCombinationId__cond ::
 Opt MRDC_Parameters_v1620__Type MRDC_Parameters_v1620__cond ::
 nil).
Definition BandCombination_v1610__cond z := 
  opt_cond BandCombination_v1610__bandList_v1610__cond (BandCombination_v1610__bandList_v1610 z) /\
  opt_cond CA_ParametersNR_v1610__cond (BandCombination_v1610__ca_ParametersNR_v1610 z) /\
  opt_cond CA_ParametersNRDC_v1610__cond (BandCombination_v1610__ca_ParametersNRDC_v1610 z) /\
  opt_cond BandCombination_v1610__powerClass_v1610__cond (BandCombination_v1610__powerClass_v1610 z) /\
  opt_cond BandCombination_v1610__powerClassNRPart_r16__cond (BandCombination_v1610__powerClassNRPart_r16 z) /\
  opt_cond FeatureSetCombinationId__cond (BandCombination_v1610__featureSetCombinationDAPS_r16 z) /\
  opt_cond MRDC_Parameters_v1620__cond (BandCombination_v1610__mrdc_Parameters_v1620 z) /\
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
Definition BandCombination_v1610__bandList_v1610__Format : T_Format BandCombination_v1610__bandList_v1610__Type BandCombination_v1610__bandList_v1610__cond := seq_of_format BandParameters_v1610__Format 1 maxSimultaneousBands BandCombination_v1610__bandList_v1610__helper1 BandCombination_v1610__bandList_v1610__helper2.

Opaque BandCombination_v1610__bandList_v1610__cond BandCombination_v1610__bandList_v1610__Format.

Definition BandCombination_v1610__powerClass_v1610__Format : T_Format BandCombination_v1610__powerClass_v1610__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandCombination_v1610__powerClass_v1610__nat__Format BandCombination_v1610__powerClass_v1610__F1 BandCombination_v1610__powerClass_v1610__F2 BandCombination_v1610__powerClass_v1610__F1F2 BandCombination_v1610__powerClass_v1610__F2F1.

Opaque BandCombination_v1610__powerClass_v1610__cond BandCombination_v1610__powerClass_v1610__Format.

Definition BandCombination_v1610__powerClassNRPart_r16__Format : T_Format BandCombination_v1610__powerClassNRPart_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandCombination_v1610__powerClassNRPart_r16__nat__Format BandCombination_v1610__powerClassNRPart_r16__F1 BandCombination_v1610__powerClassNRPart_r16__F2 BandCombination_v1610__powerClassNRPart_r16__F1F2 BandCombination_v1610__powerClassNRPart_r16__F2F1.

Opaque BandCombination_v1610__powerClassNRPart_r16__cond BandCombination_v1610__powerClassNRPart_r16__Format.


Definition BandCombination_v1610__Format_Type := Eval cbn in seq_format_prod BandCombination_v1610__list.
Definition BandCombination_v1610__Format_list : BandCombination_v1610__Format_Type :=
  (BandCombination_v1610__bandList_v1610__Format, (CA_ParametersNR_v1610__Format, (CA_ParametersNRDC_v1610__Format, (BandCombination_v1610__powerClass_v1610__Format, (BandCombination_v1610__powerClassNRPart_r16__Format, (FeatureSetCombinationId__Format, (MRDC_Parameters_v1620__Format, unit_format))))))).
Definition BandCombination_v1610__list__Format := (*Eval compute in *) seq_format BandCombination_v1610__list BandCombination_v1610__Format_list.
Definition BandCombination_v1610__F1 z :=
  (BandCombination_v1610__bandList_v1610 z, (BandCombination_v1610__ca_ParametersNR_v1610 z, (BandCombination_v1610__ca_ParametersNRDC_v1610 z, (BandCombination_v1610__powerClass_v1610 z, (BandCombination_v1610__powerClassNRPart_r16 z, (BandCombination_v1610__featureSetCombinationDAPS_r16 z, (BandCombination_v1610__mrdc_Parameters_v1620 z, tt))))))).
Definition BandCombination_v1610__F2 (y : seq_type BandCombination_v1610__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__BandCombination_v1610__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma BandCombination_v1610__F1F2_cond (z : BandCombination_v1610__Type)
  : BandCombination_v1610__cond z ->
  (seq_cond BandCombination_v1610__list (BandCombination_v1610__F1 z)).
intro H. unfold BandCombination_v1610__cond in H. simpl. auto. Qed.
Lemma BandCombination_v1610__F1F2_cond2 (z : BandCombination_v1610__Type)
 : BandCombination_v1610__F2 (BandCombination_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombination_v1610__F2F1_cond (y : seq_type BandCombination_v1610__list)
  : seq_cond BandCombination_v1610__list y ->
 (BandCombination_v1610__cond (BandCombination_v1610__F2 y)) /\  BandCombination_v1610__F1 (BandCombination_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombination_v1610__cond. simpl in *. auto.
 - simpl. unfold BandCombination_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombination_v1610__Format : T_Format BandCombination_v1610__Type BandCombination_v1610__cond :=
        proj2_format  BandCombination_v1610__cond BandCombination_v1610__list__Format
    BandCombination_v1610__F1 BandCombination_v1610__F2 BandCombination_v1610__F1F2_cond  BandCombination_v1610__F1F2_cond2 BandCombination_v1610__F2F1_cond.
Opaque BandCombination_v1610__cond BandCombination_v1610__Format.

