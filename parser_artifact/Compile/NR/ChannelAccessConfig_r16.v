Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__helper1 : (-85 <= -52)%Z.  lia. Qed.
Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__helper2 : to_bit_sz (Z.to_nat (-52 - -85)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-52 - -85))%Z). { apply Zorder.Zle_minus_le_0. apply ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__Type := Z.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__cond := (fun z => (-85 <= z <= -52)%Z).
Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__helper1 : (-13 <= 20)%Z.  lia. Qed.
Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__helper2 : to_bit_sz (Z.to_nat (20 - -13)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20 - -13))%Z). { apply Zorder.Zle_minus_le_0. apply ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__Type := Z.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__cond := (fun z => (-13 <= z <= 20)%Z).

Inductive ChannelAccessConfig_r16__energyDetectionConfig_r16__Type : Set :=
  | ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16 : Z -> ChannelAccessConfig_r16__energyDetectionConfig_r16__Type
  | ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16 : Z -> ChannelAccessConfig_r16__energyDetectionConfig_r16__Type
.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__list : list typ := (
typ_cons Z ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__cond ::
typ_cons Z ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__cond ::
 nil).
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__cond (c : ChannelAccessConfig_r16__energyDetectionConfig_r16__Type) := 
  match c with
  | ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16 t => ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__cond t 
  | ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16 t => ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__cond t 
  end.

Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__len_helper1 : to_bit_sz (length ChannelAccessConfig_r16__energyDetectionConfig_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__len_helper2 : 2 <= length2 ChannelAccessConfig_r16__energyDetectionConfig_r16__list.
 simpl. lia. Qed.
Lemma ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__helper1 : (-85 <= -52)%Z.  lia. Qed.
Lemma ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__helper2 : to_bit_sz (Z.to_nat (-52 - -85)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-52 - -85))%Z). { apply Zorder.Zle_minus_le_0. apply ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__Type := Z.
Definition ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__cond := (fun z => (-85 <= z <= -52)%Z).
Inductive ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Type : Set :=
 | ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__true
.
Definition ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__cond := (fun (_ : ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Type) => True).
Lemma ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__nat__helper.

Definition ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F1 t :=
  match t with
  | ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__true => 0
  end.
Definition ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F2 n :=
  match n with
  | 0 => ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__true
  | _ => ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__true
  end.
Lemma ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F1F2 : forall x : ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Type, (ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F1 x <= 0) /\ ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F2 (ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F1 x) = x. imp_solve. Qed.
Lemma ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F2F1 : forall (y : nat) (H : y <= 0), ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F1 (ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F2 y) = y. enum_solve H y. Qed.

Record ChannelAccessConfig_r16__Type : Set :=
  make__ChannelAccessConfig_r16__Type {
    ChannelAccessConfig_r16__energyDetectionConfig_r16 : option ChannelAccessConfig_r16__energyDetectionConfig_r16__Type ;
    ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16 : option Z ;
    ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16 : option ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Type ;
}.
Definition ChannelAccessConfig_r16__list := (
 Opt ChannelAccessConfig_r16__energyDetectionConfig_r16__Type ChannelAccessConfig_r16__energyDetectionConfig_r16__cond ::
 Opt Z ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__cond ::
 Opt ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Type ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__cond ::
 nil).
Definition ChannelAccessConfig_r16__cond z := 
  opt_cond ChannelAccessConfig_r16__energyDetectionConfig_r16__cond (ChannelAccessConfig_r16__energyDetectionConfig_r16 z) /\
  opt_cond ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__cond (ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16 z) /\
  opt_cond ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__cond (ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16 z) /\
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
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__Format : T_Format Z ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__cond :=
 ranged_int_format (-85) (-52) ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__helper1 ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__helper2.

Opaque ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__cond ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__Format.

Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__Format : T_Format Z ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__cond :=
 ranged_int_format (-13) (20) ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__helper1 ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__helper2.

Opaque ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__cond ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__Format.


Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__Format_Type := Eval cbn in get_formats ChannelAccessConfig_r16__energyDetectionConfig_r16__list.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__Format_list : ChannelAccessConfig_r16__energyDetectionConfig_r16__Format_Type :=
  (ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16__Format, (ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16__Format, unit__Format)).
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__list__Format := Eval compute in choice_format ChannelAccessConfig_r16__energyDetectionConfig_r16__list ChannelAccessConfig_r16__energyDetectionConfig_r16__len_helper1 ChannelAccessConfig_r16__energyDetectionConfig_r16__len_helper2  ChannelAccessConfig_r16__energyDetectionConfig_r16__Format_list.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__F1 (z : ChannelAccessConfig_r16__energyDetectionConfig_r16__Type) : (choice ChannelAccessConfig_r16__energyDetectionConfig_r16__list) :=
  match z with
   | ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16 t => existT _ 0 t
  | ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16 t => existT _ 1 t
  end.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__g := (fun n => typ_set (get_nth_typ ChannelAccessConfig_r16__energyDetectionConfig_r16__list n)).
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__F2 (y : choice ChannelAccessConfig_r16__energyDetectionConfig_r16__list) : ChannelAccessConfig_r16__energyDetectionConfig_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ChannelAccessConfig_r16__energyDetectionConfig_r16__g n -> ChannelAccessConfig_r16__energyDetectionConfig_r16__Type) with
    | 0 => fun (t : Z) => ChannelAccessConfig_r16__energyDetectionConfig_r16__maxEnergyDetectionThreshold_r16 t 
    | 1 => fun (t : Z) => ChannelAccessConfig_r16__energyDetectionConfig_r16__energyDetectionThresholdOffset_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ChannelAccessConfig_r16__energyDetectionConfig_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ChannelAccessConfig_r16__energyDetectionConfig_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ChannelAccessConfig_r16__energyDetectionConfig_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ChannelAccessConfig_r16__energyDetectionConfig_r16__Type with end) n0
           end t0).

Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__helper2 :  forall (y : ChannelAccessConfig_r16__energyDetectionConfig_r16__Type), ChannelAccessConfig_r16__energyDetectionConfig_r16__cond y -> choice_cond ChannelAccessConfig_r16__energyDetectionConfig_r16__list (ChannelAccessConfig_r16__energyDetectionConfig_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__helper3 :  forall (y : ChannelAccessConfig_r16__energyDetectionConfig_r16__Type), ChannelAccessConfig_r16__energyDetectionConfig_r16__F2 (ChannelAccessConfig_r16__energyDetectionConfig_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ChannelAccessConfig_r16__energyDetectionConfig_r16__helper4 : (forall b : choice ChannelAccessConfig_r16__energyDetectionConfig_r16__list, choice_cond ChannelAccessConfig_r16__energyDetectionConfig_r16__list b -> ChannelAccessConfig_r16__energyDetectionConfig_r16__cond (ChannelAccessConfig_r16__energyDetectionConfig_r16__F2 b) /\ ChannelAccessConfig_r16__energyDetectionConfig_r16__F1 (ChannelAccessConfig_r16__energyDetectionConfig_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ChannelAccessConfig_r16__energyDetectionConfig_r16__F1 ChannelAccessConfig_r16__energyDetectionConfig_r16__F2.
Definition ChannelAccessConfig_r16__energyDetectionConfig_r16__Format : T_Format ChannelAccessConfig_r16__energyDetectionConfig_r16__Type ChannelAccessConfig_r16__energyDetectionConfig_r16__cond :=
  (* Eval compute in *) proj2_format ChannelAccessConfig_r16__energyDetectionConfig_r16__cond ChannelAccessConfig_r16__energyDetectionConfig_r16__list__Format ChannelAccessConfig_r16__energyDetectionConfig_r16__F1 ChannelAccessConfig_r16__energyDetectionConfig_r16__F2 ChannelAccessConfig_r16__energyDetectionConfig_r16__helper2 ChannelAccessConfig_r16__energyDetectionConfig_r16__helper3 ChannelAccessConfig_r16__energyDetectionConfig_r16__helper4.
Opaque ChannelAccessConfig_r16__energyDetectionConfig_r16__cond ChannelAccessConfig_r16__energyDetectionConfig_r16__Format.

Definition ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__Format : T_Format Z ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__cond :=
 ranged_int_format (-85) (-52) ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__helper1 ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__helper2.

Opaque ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__cond ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__Format.

Definition ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Format : T_Format ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__nat__Format ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F1 ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F2 ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F1F2 ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__F2F1.

Opaque ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__cond ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Format.


Definition ChannelAccessConfig_r16__Format_Type := Eval cbn in seq_format_prod ChannelAccessConfig_r16__list.
Definition ChannelAccessConfig_r16__Format_list : ChannelAccessConfig_r16__Format_Type :=
  (ChannelAccessConfig_r16__energyDetectionConfig_r16__Format, (ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16__Format, (ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16__Format, unit_format))).
Definition ChannelAccessConfig_r16__list__Format := (*Eval compute in *) seq_format ChannelAccessConfig_r16__list ChannelAccessConfig_r16__Format_list.
Definition ChannelAccessConfig_r16__F1 z :=
  (ChannelAccessConfig_r16__energyDetectionConfig_r16 z, (ChannelAccessConfig_r16__ul_toDL_COT_SharingED_Threshold_r16 z, (ChannelAccessConfig_r16__absenceOfAnyOtherTechnology_r16 z, tt))).
Definition ChannelAccessConfig_r16__F2 (y : seq_type ChannelAccessConfig_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ChannelAccessConfig_r16__Type i0 i1 i2
  end.
Lemma ChannelAccessConfig_r16__F1F2_cond (z : ChannelAccessConfig_r16__Type)
  : ChannelAccessConfig_r16__cond z ->
  (seq_cond ChannelAccessConfig_r16__list (ChannelAccessConfig_r16__F1 z)).
intro H. unfold ChannelAccessConfig_r16__cond in H. simpl. auto. Qed.
Lemma ChannelAccessConfig_r16__F1F2_cond2 (z : ChannelAccessConfig_r16__Type)
 : ChannelAccessConfig_r16__F2 (ChannelAccessConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ChannelAccessConfig_r16__F2F1_cond (y : seq_type ChannelAccessConfig_r16__list)
  : seq_cond ChannelAccessConfig_r16__list y ->
 (ChannelAccessConfig_r16__cond (ChannelAccessConfig_r16__F2 y)) /\  ChannelAccessConfig_r16__F1 (ChannelAccessConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ChannelAccessConfig_r16__cond. simpl in *. auto.
 - simpl. unfold ChannelAccessConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ChannelAccessConfig_r16__Format : T_Format ChannelAccessConfig_r16__Type ChannelAccessConfig_r16__cond :=
        proj2_format  ChannelAccessConfig_r16__cond ChannelAccessConfig_r16__list__Format
    ChannelAccessConfig_r16__F1 ChannelAccessConfig_r16__F2 ChannelAccessConfig_r16__F1F2_cond  ChannelAccessConfig_r16__F1F2_cond2 ChannelAccessConfig_r16__F2F1_cond.
Opaque ChannelAccessConfig_r16__cond ChannelAccessConfig_r16__Format.

