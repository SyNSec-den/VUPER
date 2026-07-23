Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DummyJ__maxEnergyDetectionThreshold_r16__helper1 : (-85 <= -52)%Z.  lia. Qed.
Lemma DummyJ__maxEnergyDetectionThreshold_r16__helper2 : to_bit_sz (Z.to_nat (-52 - -85)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-52 - -85))%Z). { apply Zorder.Zle_minus_le_0. apply DummyJ__maxEnergyDetectionThreshold_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyJ__maxEnergyDetectionThreshold_r16__Type := Z.
Definition DummyJ__maxEnergyDetectionThreshold_r16__cond := (fun z => (-85 <= z <= -52)%Z).
Lemma DummyJ__energyDetectionThresholdOffset_r16__helper1 : (-20 <= -13)%Z.  lia. Qed.
Lemma DummyJ__energyDetectionThresholdOffset_r16__helper2 : to_bit_sz (Z.to_nat (-13 - -20)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-13 - -20))%Z). { apply Zorder.Zle_minus_le_0. apply DummyJ__energyDetectionThresholdOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyJ__energyDetectionThresholdOffset_r16__Type := Z.
Definition DummyJ__energyDetectionThresholdOffset_r16__cond := (fun z => (-20 <= z <= -13)%Z).
Lemma DummyJ__ul_toDL_COT_SharingED_Threshold_r16__helper1 : (-85 <= -52)%Z.  lia. Qed.
Lemma DummyJ__ul_toDL_COT_SharingED_Threshold_r16__helper2 : to_bit_sz (Z.to_nat (-52 - -85)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-52 - -85))%Z). { apply Zorder.Zle_minus_le_0. apply DummyJ__ul_toDL_COT_SharingED_Threshold_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyJ__ul_toDL_COT_SharingED_Threshold_r16__Type := Z.
Definition DummyJ__ul_toDL_COT_SharingED_Threshold_r16__cond := (fun z => (-85 <= z <= -52)%Z).
Inductive DummyJ__absenceOfAnyOtherTechnology_r16__Type : Set :=
 | DummyJ__absenceOfAnyOtherTechnology_r16__true
.
Definition DummyJ__absenceOfAnyOtherTechnology_r16__cond := (fun (_ : DummyJ__absenceOfAnyOtherTechnology_r16__Type) => True).
Lemma DummyJ__absenceOfAnyOtherTechnology_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyJ__absenceOfAnyOtherTechnology_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DummyJ__absenceOfAnyOtherTechnology_r16__nat__helper.

Definition DummyJ__absenceOfAnyOtherTechnology_r16__F1 t :=
  match t with
  | DummyJ__absenceOfAnyOtherTechnology_r16__true => 0
  end.
Definition DummyJ__absenceOfAnyOtherTechnology_r16__F2 n :=
  match n with
  | 0 => DummyJ__absenceOfAnyOtherTechnology_r16__true
  | _ => DummyJ__absenceOfAnyOtherTechnology_r16__true
  end.
Lemma DummyJ__absenceOfAnyOtherTechnology_r16__F1F2 : forall x : DummyJ__absenceOfAnyOtherTechnology_r16__Type, (DummyJ__absenceOfAnyOtherTechnology_r16__F1 x <= 0) /\ DummyJ__absenceOfAnyOtherTechnology_r16__F2 (DummyJ__absenceOfAnyOtherTechnology_r16__F1 x) = x. imp_solve. Qed.
Lemma DummyJ__absenceOfAnyOtherTechnology_r16__F2F1 : forall (y : nat) (H : y <= 0), DummyJ__absenceOfAnyOtherTechnology_r16__F1 (DummyJ__absenceOfAnyOtherTechnology_r16__F2 y) = y. enum_solve H y. Qed.

Record DummyJ__Type : Set :=
  make__DummyJ__Type {
    DummyJ__maxEnergyDetectionThreshold_r16 : Z ;
    DummyJ__energyDetectionThresholdOffset_r16 : Z ;
    DummyJ__ul_toDL_COT_SharingED_Threshold_r16 : option Z ;
    DummyJ__absenceOfAnyOtherTechnology_r16 : option DummyJ__absenceOfAnyOtherTechnology_r16__Type ;
}.
Definition DummyJ__list := (
 Nor Z DummyJ__maxEnergyDetectionThreshold_r16__cond ::
 Nor Z DummyJ__energyDetectionThresholdOffset_r16__cond ::
 Opt Z DummyJ__ul_toDL_COT_SharingED_Threshold_r16__cond ::
 Opt DummyJ__absenceOfAnyOtherTechnology_r16__Type DummyJ__absenceOfAnyOtherTechnology_r16__cond ::
 nil).
Definition DummyJ__cond z := 
  DummyJ__maxEnergyDetectionThreshold_r16__cond (DummyJ__maxEnergyDetectionThreshold_r16 z) /\
  DummyJ__energyDetectionThresholdOffset_r16__cond (DummyJ__energyDetectionThresholdOffset_r16 z) /\
  opt_cond DummyJ__ul_toDL_COT_SharingED_Threshold_r16__cond (DummyJ__ul_toDL_COT_SharingED_Threshold_r16 z) /\
  opt_cond DummyJ__absenceOfAnyOtherTechnology_r16__cond (DummyJ__absenceOfAnyOtherTechnology_r16 z) /\
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
Definition DummyJ__maxEnergyDetectionThreshold_r16__Format : T_Format Z DummyJ__maxEnergyDetectionThreshold_r16__cond :=
 ranged_int_format (-85) (-52) DummyJ__maxEnergyDetectionThreshold_r16__helper1 DummyJ__maxEnergyDetectionThreshold_r16__helper2.

Opaque DummyJ__maxEnergyDetectionThreshold_r16__cond DummyJ__maxEnergyDetectionThreshold_r16__Format.

Definition DummyJ__energyDetectionThresholdOffset_r16__Format : T_Format Z DummyJ__energyDetectionThresholdOffset_r16__cond :=
 ranged_int_format (-20) (-13) DummyJ__energyDetectionThresholdOffset_r16__helper1 DummyJ__energyDetectionThresholdOffset_r16__helper2.

Opaque DummyJ__energyDetectionThresholdOffset_r16__cond DummyJ__energyDetectionThresholdOffset_r16__Format.

Definition DummyJ__ul_toDL_COT_SharingED_Threshold_r16__Format : T_Format Z DummyJ__ul_toDL_COT_SharingED_Threshold_r16__cond :=
 ranged_int_format (-85) (-52) DummyJ__ul_toDL_COT_SharingED_Threshold_r16__helper1 DummyJ__ul_toDL_COT_SharingED_Threshold_r16__helper2.

Opaque DummyJ__ul_toDL_COT_SharingED_Threshold_r16__cond DummyJ__ul_toDL_COT_SharingED_Threshold_r16__Format.

Definition DummyJ__absenceOfAnyOtherTechnology_r16__Format : T_Format DummyJ__absenceOfAnyOtherTechnology_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyJ__absenceOfAnyOtherTechnology_r16__nat__Format DummyJ__absenceOfAnyOtherTechnology_r16__F1 DummyJ__absenceOfAnyOtherTechnology_r16__F2 DummyJ__absenceOfAnyOtherTechnology_r16__F1F2 DummyJ__absenceOfAnyOtherTechnology_r16__F2F1.

Opaque DummyJ__absenceOfAnyOtherTechnology_r16__cond DummyJ__absenceOfAnyOtherTechnology_r16__Format.


Definition DummyJ__Format_Type := Eval cbn in seq_format_prod DummyJ__list.
Definition DummyJ__Format_list : DummyJ__Format_Type :=
  (DummyJ__maxEnergyDetectionThreshold_r16__Format, (DummyJ__energyDetectionThresholdOffset_r16__Format, (DummyJ__ul_toDL_COT_SharingED_Threshold_r16__Format, (DummyJ__absenceOfAnyOtherTechnology_r16__Format, unit_format)))).
Definition DummyJ__list__Format := (*Eval compute in *) seq_format DummyJ__list DummyJ__Format_list.
Definition DummyJ__F1 z :=
  (DummyJ__maxEnergyDetectionThreshold_r16 z, (DummyJ__energyDetectionThresholdOffset_r16 z, (DummyJ__ul_toDL_COT_SharingED_Threshold_r16 z, (DummyJ__absenceOfAnyOtherTechnology_r16 z, tt)))).
Definition DummyJ__F2 (y : seq_type DummyJ__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__DummyJ__Type i0 i1 i2 i3
  end.
Lemma DummyJ__F1F2_cond (z : DummyJ__Type)
  : DummyJ__cond z ->
  (seq_cond DummyJ__list (DummyJ__F1 z)).
intro H. unfold DummyJ__cond in H. simpl. auto. Qed.
Lemma DummyJ__F1F2_cond2 (z : DummyJ__Type)
 : DummyJ__F2 (DummyJ__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyJ__F2F1_cond (y : seq_type DummyJ__list)
  : seq_cond DummyJ__list y ->
 (DummyJ__cond (DummyJ__F2 y)) /\  DummyJ__F1 (DummyJ__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyJ__cond. simpl in *. auto.
 - simpl. unfold DummyJ__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyJ__Format : T_Format DummyJ__Type DummyJ__cond :=
        proj2_format  DummyJ__cond DummyJ__list__Format
    DummyJ__F1 DummyJ__F2 DummyJ__F1F2_cond  DummyJ__F1F2_cond2 DummyJ__F2F1_cond.
Opaque DummyJ__cond DummyJ__Format.

