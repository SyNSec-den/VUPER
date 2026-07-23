Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUCCH_PowerControl__deltaF_PUCCH_f0__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma PUCCH_PowerControl__deltaF_PUCCH_f0__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_PowerControl__deltaF_PUCCH_f0__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_PowerControl__deltaF_PUCCH_f0__Type := Z.
Definition PUCCH_PowerControl__deltaF_PUCCH_f0__cond := (fun z => (-16 <= z <= 15)%Z).
Lemma PUCCH_PowerControl__deltaF_PUCCH_f1__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma PUCCH_PowerControl__deltaF_PUCCH_f1__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_PowerControl__deltaF_PUCCH_f1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_PowerControl__deltaF_PUCCH_f1__Type := Z.
Definition PUCCH_PowerControl__deltaF_PUCCH_f1__cond := (fun z => (-16 <= z <= 15)%Z).
Lemma PUCCH_PowerControl__deltaF_PUCCH_f2__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma PUCCH_PowerControl__deltaF_PUCCH_f2__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_PowerControl__deltaF_PUCCH_f2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_PowerControl__deltaF_PUCCH_f2__Type := Z.
Definition PUCCH_PowerControl__deltaF_PUCCH_f2__cond := (fun z => (-16 <= z <= 15)%Z).
Lemma PUCCH_PowerControl__deltaF_PUCCH_f3__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma PUCCH_PowerControl__deltaF_PUCCH_f3__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_PowerControl__deltaF_PUCCH_f3__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_PowerControl__deltaF_PUCCH_f3__Type := Z.
Definition PUCCH_PowerControl__deltaF_PUCCH_f3__cond := (fun z => (-16 <= z <= 15)%Z).
Lemma PUCCH_PowerControl__deltaF_PUCCH_f4__helper1 : (-16 <= 15)%Z.  lia. Qed.
Lemma PUCCH_PowerControl__deltaF_PUCCH_f4__helper2 : to_bit_sz (Z.to_nat (15 - -16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -16))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_PowerControl__deltaF_PUCCH_f4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_PowerControl__deltaF_PUCCH_f4__Type := Z.
Definition PUCCH_PowerControl__deltaF_PUCCH_f4__cond := (fun z => (-16 <= z <= 15)%Z).
Require Import NR.P0_PUCCH.

Opaque P0_PUCCH__cond P0_PUCCH__Format.

Definition PUCCH_PowerControl__p0_Set__Type := list P0_PUCCH__Type.

Lemma PUCCH_PowerControl__p0_Set__helper1 : (0 <= 1 <= maxNrofPUCCH_P0_PerSet)%Z. unfold maxNrofPUCCH_P0_PerSet.
 lia. Qed.
Lemma PUCCH_PowerControl__p0_Set__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_P0_PerSet - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_P0_PerSet - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_PowerControl__p0_Set__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_PowerControl__p0_Set__cond (z : PUCCH_PowerControl__p0_Set__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_P0_PerSet)%Z /\ (list_and P0_PUCCH__cond z) .

Require Import NR.PUCCH_PathlossReferenceRS.

Opaque PUCCH_PathlossReferenceRS__cond PUCCH_PathlossReferenceRS__Format.

Definition PUCCH_PowerControl__pathlossReferenceRSs__Type := list PUCCH_PathlossReferenceRS__Type.

Lemma PUCCH_PowerControl__pathlossReferenceRSs__helper1 : (0 <= 1 <= maxNrofPUCCH_PathlossReferenceRSs)%Z. unfold maxNrofPUCCH_PathlossReferenceRSs.
 lia. Qed.
Lemma PUCCH_PowerControl__pathlossReferenceRSs__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_PathlossReferenceRSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_PathlossReferenceRSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_PowerControl__pathlossReferenceRSs__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_PowerControl__pathlossReferenceRSs__cond (z : PUCCH_PowerControl__pathlossReferenceRSs__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_PathlossReferenceRSs)%Z /\ (list_and PUCCH_PathlossReferenceRS__cond z) .

Inductive PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Type : Set :=
 | PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__twoStates
.
Definition PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__cond := (fun (_ : PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Type) => True).
Lemma PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__nat__helper.

Definition PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F1 t :=
  match t with
  | PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__twoStates => 0
  end.
Definition PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F2 n :=
  match n with
  | 0 => PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__twoStates
  | _ => PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__twoStates
  end.
Lemma PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F1F2 : forall x : PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Type, (PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F1 x <= 0) /\ PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F2 (PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F1 (PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PathlossReferenceRSs_v1610.
Definition PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__Type := SetupRelease__Type PathlossReferenceRSs_v1610__Type.
Definition PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__cond := SetupRelease__cond _ PathlossReferenceRSs_v1610__cond.
Definition PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__Format : T_Format PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__Type PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__cond := SetupRelease__Format _ _ PathlossReferenceRSs_v1610__Format.
Opaque PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__cond PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__Format.

Record PUCCH_PowerControl__ext0O__Type : Set :=
  make__PUCCH_PowerControl__ext0O__Type {
    PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610 : option PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__Type ;
}.
Definition PUCCH_PowerControl__ext0O__list := (
 Opt PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__Type PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__cond ::
 nil).
Definition PUCCH_PowerControl__ext0O__cond z := 
  opt_cond PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__cond (PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610 z) /\
  True.

Definition PUCCH_PowerControl__ext0__Type := PUCCH_PowerControl__ext0O__Type.
Definition PUCCH_PowerControl__ext0__cond := PUCCH_PowerControl__ext0O__cond.

Record PUCCH_PowerControl__Type : Set :=
  make__PUCCH_PowerControl__Type {
    PUCCH_PowerControl__deltaF_PUCCH_f0 : option Z ;
    PUCCH_PowerControl__deltaF_PUCCH_f1 : option Z ;
    PUCCH_PowerControl__deltaF_PUCCH_f2 : option Z ;
    PUCCH_PowerControl__deltaF_PUCCH_f3 : option Z ;
    PUCCH_PowerControl__deltaF_PUCCH_f4 : option Z ;
    PUCCH_PowerControl__p0_Set : option PUCCH_PowerControl__p0_Set__Type ;
    PUCCH_PowerControl__pathlossReferenceRSs : option PUCCH_PowerControl__pathlossReferenceRSs__Type ;
    PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates : option PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Type ;
    PUCCH_PowerControl__ext0 : option PUCCH_PowerControl__ext0__Type ;
}.
Definition PUCCH_PowerControl__root_list : list seq_elem := (
 Opt Z PUCCH_PowerControl__deltaF_PUCCH_f0__cond ::
 Opt Z PUCCH_PowerControl__deltaF_PUCCH_f1__cond ::
 Opt Z PUCCH_PowerControl__deltaF_PUCCH_f2__cond ::
 Opt Z PUCCH_PowerControl__deltaF_PUCCH_f3__cond ::
 Opt Z PUCCH_PowerControl__deltaF_PUCCH_f4__cond ::
 Opt PUCCH_PowerControl__p0_Set__Type PUCCH_PowerControl__p0_Set__cond ::
 Opt PUCCH_PowerControl__pathlossReferenceRSs__Type PUCCH_PowerControl__pathlossReferenceRSs__cond ::
 Opt PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Type PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__cond ::
 nil).
Definition PUCCH_PowerControl__ext_list : list typ := (
  typ_cons PUCCH_PowerControl__ext0__Type PUCCH_PowerControl__ext0__cond ::
  nil).
Definition PUCCH_PowerControl__cond (z : PUCCH_PowerControl__Type) := 
(  opt_cond PUCCH_PowerControl__deltaF_PUCCH_f0__cond (PUCCH_PowerControl__deltaF_PUCCH_f0 z) /\
  opt_cond PUCCH_PowerControl__deltaF_PUCCH_f1__cond (PUCCH_PowerControl__deltaF_PUCCH_f1 z) /\
  opt_cond PUCCH_PowerControl__deltaF_PUCCH_f2__cond (PUCCH_PowerControl__deltaF_PUCCH_f2 z) /\
  opt_cond PUCCH_PowerControl__deltaF_PUCCH_f3__cond (PUCCH_PowerControl__deltaF_PUCCH_f3 z) /\
  opt_cond PUCCH_PowerControl__deltaF_PUCCH_f4__cond (PUCCH_PowerControl__deltaF_PUCCH_f4 z) /\
  opt_cond PUCCH_PowerControl__p0_Set__cond (PUCCH_PowerControl__p0_Set z) /\
  opt_cond PUCCH_PowerControl__pathlossReferenceRSs__cond (PUCCH_PowerControl__pathlossReferenceRSs z) /\
  opt_cond PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__cond (PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates z) /\
  True) /\ 
(  opt_cond PUCCH_PowerControl__ext0__cond (PUCCH_PowerControl__ext0 z) /\
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
Definition PUCCH_PowerControl__deltaF_PUCCH_f0__Format : T_Format Z PUCCH_PowerControl__deltaF_PUCCH_f0__cond :=
 ranged_int_format (-16) (15) PUCCH_PowerControl__deltaF_PUCCH_f0__helper1 PUCCH_PowerControl__deltaF_PUCCH_f0__helper2.

Opaque PUCCH_PowerControl__deltaF_PUCCH_f0__cond PUCCH_PowerControl__deltaF_PUCCH_f0__Format.

Definition PUCCH_PowerControl__deltaF_PUCCH_f1__Format : T_Format Z PUCCH_PowerControl__deltaF_PUCCH_f1__cond :=
 ranged_int_format (-16) (15) PUCCH_PowerControl__deltaF_PUCCH_f1__helper1 PUCCH_PowerControl__deltaF_PUCCH_f1__helper2.

Opaque PUCCH_PowerControl__deltaF_PUCCH_f1__cond PUCCH_PowerControl__deltaF_PUCCH_f1__Format.

Definition PUCCH_PowerControl__deltaF_PUCCH_f2__Format : T_Format Z PUCCH_PowerControl__deltaF_PUCCH_f2__cond :=
 ranged_int_format (-16) (15) PUCCH_PowerControl__deltaF_PUCCH_f2__helper1 PUCCH_PowerControl__deltaF_PUCCH_f2__helper2.

Opaque PUCCH_PowerControl__deltaF_PUCCH_f2__cond PUCCH_PowerControl__deltaF_PUCCH_f2__Format.

Definition PUCCH_PowerControl__deltaF_PUCCH_f3__Format : T_Format Z PUCCH_PowerControl__deltaF_PUCCH_f3__cond :=
 ranged_int_format (-16) (15) PUCCH_PowerControl__deltaF_PUCCH_f3__helper1 PUCCH_PowerControl__deltaF_PUCCH_f3__helper2.

Opaque PUCCH_PowerControl__deltaF_PUCCH_f3__cond PUCCH_PowerControl__deltaF_PUCCH_f3__Format.

Definition PUCCH_PowerControl__deltaF_PUCCH_f4__Format : T_Format Z PUCCH_PowerControl__deltaF_PUCCH_f4__cond :=
 ranged_int_format (-16) (15) PUCCH_PowerControl__deltaF_PUCCH_f4__helper1 PUCCH_PowerControl__deltaF_PUCCH_f4__helper2.

Opaque PUCCH_PowerControl__deltaF_PUCCH_f4__cond PUCCH_PowerControl__deltaF_PUCCH_f4__Format.

Definition PUCCH_PowerControl__p0_Set__Format : T_Format PUCCH_PowerControl__p0_Set__Type PUCCH_PowerControl__p0_Set__cond := seq_of_format P0_PUCCH__Format 1 maxNrofPUCCH_P0_PerSet PUCCH_PowerControl__p0_Set__helper1 PUCCH_PowerControl__p0_Set__helper2.

Opaque PUCCH_PowerControl__p0_Set__cond PUCCH_PowerControl__p0_Set__Format.

Definition PUCCH_PowerControl__pathlossReferenceRSs__Format : T_Format PUCCH_PowerControl__pathlossReferenceRSs__Type PUCCH_PowerControl__pathlossReferenceRSs__cond := seq_of_format PUCCH_PathlossReferenceRS__Format 1 maxNrofPUCCH_PathlossReferenceRSs PUCCH_PowerControl__pathlossReferenceRSs__helper1 PUCCH_PowerControl__pathlossReferenceRSs__helper2.

Opaque PUCCH_PowerControl__pathlossReferenceRSs__cond PUCCH_PowerControl__pathlossReferenceRSs__Format.

Definition PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Format : T_Format PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__nat__Format PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F1 PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F2 PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F1F2 PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__F2F1.

Opaque PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__cond PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Format.

Opaque PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__cond PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__Format.


Definition PUCCH_PowerControl__ext0O__Format_Type := Eval cbn in seq_format_prod PUCCH_PowerControl__ext0O__list.
Definition PUCCH_PowerControl__ext0O__Format_list : PUCCH_PowerControl__ext0O__Format_Type :=
  (PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610__Format, unit_format).
Definition PUCCH_PowerControl__ext0O__list__Format := (*Eval compute in *) seq_format PUCCH_PowerControl__ext0O__list PUCCH_PowerControl__ext0O__Format_list.
Definition PUCCH_PowerControl__ext0O__F1 z :=
  (PUCCH_PowerControl__ext0O__pathlossReferenceRSs_v1610 z, tt).
Definition PUCCH_PowerControl__ext0O__F2 (y : seq_type PUCCH_PowerControl__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PUCCH_PowerControl__ext0O__Type i0
  end.
Lemma PUCCH_PowerControl__ext0O__F1F2_cond (z : PUCCH_PowerControl__ext0O__Type)
  : PUCCH_PowerControl__ext0O__cond z ->
  (seq_cond PUCCH_PowerControl__ext0O__list (PUCCH_PowerControl__ext0O__F1 z)).
intro H. unfold PUCCH_PowerControl__ext0O__cond in H. simpl. auto. Qed.
Lemma PUCCH_PowerControl__ext0O__F1F2_cond2 (z : PUCCH_PowerControl__ext0O__Type)
 : PUCCH_PowerControl__ext0O__F2 (PUCCH_PowerControl__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_PowerControl__ext0O__F2F1_cond (y : seq_type PUCCH_PowerControl__ext0O__list)
  : seq_cond PUCCH_PowerControl__ext0O__list y ->
 (PUCCH_PowerControl__ext0O__cond (PUCCH_PowerControl__ext0O__F2 y)) /\  PUCCH_PowerControl__ext0O__F1 (PUCCH_PowerControl__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_PowerControl__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUCCH_PowerControl__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_PowerControl__ext0O__Format : T_Format PUCCH_PowerControl__ext0O__Type PUCCH_PowerControl__ext0O__cond :=
        proj2_format  PUCCH_PowerControl__ext0O__cond PUCCH_PowerControl__ext0O__list__Format
    PUCCH_PowerControl__ext0O__F1 PUCCH_PowerControl__ext0O__F2 PUCCH_PowerControl__ext0O__F1F2_cond  PUCCH_PowerControl__ext0O__F1F2_cond2 PUCCH_PowerControl__ext0O__F2F1_cond.
Opaque PUCCH_PowerControl__ext0O__cond PUCCH_PowerControl__ext0O__Format.

Definition PUCCH_PowerControl__ext0__check_all_none (b : PUCCH_PowerControl__ext0O__Type) : bool :=
match b with 
  | make__PUCCH_PowerControl__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PUCCH_PowerControl__ext0__Format : T_Format PUCCH_PowerControl__ext0__Type PUCCH_PowerControl__ext0__cond :=
  restrict_add_format PUCCH_PowerControl__ext0__check_all_none PUCCH_PowerControl__ext0O__Format.

Opaque PUCCH_PowerControl__ext0__cond PUCCH_PowerControl__ext0__Format.


Definition PUCCH_PowerControl__root_Format_Type := Eval cbn in seq_format_prod PUCCH_PowerControl__root_list.
Definition PUCCH_PowerControl__root_Format_list : PUCCH_PowerControl__root_Format_Type :=
  (PUCCH_PowerControl__deltaF_PUCCH_f0__Format, (PUCCH_PowerControl__deltaF_PUCCH_f1__Format, (PUCCH_PowerControl__deltaF_PUCCH_f2__Format, (PUCCH_PowerControl__deltaF_PUCCH_f3__Format, (PUCCH_PowerControl__deltaF_PUCCH_f4__Format, (PUCCH_PowerControl__p0_Set__Format, (PUCCH_PowerControl__pathlossReferenceRSs__Format, (PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates__Format, unit_format)))))))).

Definition PUCCH_PowerControl__ext_Format_Type := Eval cbn in get_formats PUCCH_PowerControl__ext_list.
Definition PUCCH_PowerControl__ext_Format_list : PUCCH_PowerControl__ext_Format_Type :=
  (PUCCH_PowerControl__ext0__Format, unit__Format).

Definition PUCCH_PowerControl__list_type : Set := (seq_type PUCCH_PowerControl__root_list) * (seq_ext_type PUCCH_PowerControl__ext_list).
Definition PUCCH_PowerControl__list_cond (z : PUCCH_PowerControl__list_type) : Prop :=
        (seq_cond PUCCH_PowerControl__root_list (fst z)) /\ (seq_ext_cond PUCCH_PowerControl__ext_list (snd z)).
Definition PUCCH_PowerControl__list_format : T_Format PUCCH_PowerControl__list_type PUCCH_PowerControl__list_cond :=
 (* Eval compute in *) seq_ext_format PUCCH_PowerControl__root_list PUCCH_PowerControl__root_Format_list PUCCH_PowerControl__ext_list PUCCH_PowerControl__ext_Format_list.

Opaque PUCCH_PowerControl__list_format.
Definition PUCCH_PowerControl__F1 (z : PUCCH_PowerControl__Type) : PUCCH_PowerControl__list_type :=
  (((PUCCH_PowerControl__deltaF_PUCCH_f0 z, (PUCCH_PowerControl__deltaF_PUCCH_f1 z, (PUCCH_PowerControl__deltaF_PUCCH_f2 z, (PUCCH_PowerControl__deltaF_PUCCH_f3 z, (PUCCH_PowerControl__deltaF_PUCCH_f4 z, (PUCCH_PowerControl__p0_Set z, (PUCCH_PowerControl__pathlossReferenceRSs z, (PUCCH_PowerControl__twoPUCCH_PC_AdjustmentStates z, tt))))))))), (
(PUCCH_PowerControl__ext0 z, tt))).
Definition PUCCH_PowerControl__F2 (y : PUCCH_PowerControl__list_type) : PUCCH_PowerControl__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, _))=>
    make__PUCCH_PowerControl__Type j0 j1 j2 j3 j4 j5 j6 j7 i0
  end.
Definition PUCCH_PowerControl__helper1 : (forall a : PUCCH_PowerControl__Type, PUCCH_PowerControl__cond a -> PUCCH_PowerControl__list_cond (PUCCH_PowerControl__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUCCH_PowerControl__helper2 : (forall a : PUCCH_PowerControl__Type, PUCCH_PowerControl__F2 (PUCCH_PowerControl__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUCCH_PowerControl__helper3 : (forall b : PUCCH_PowerControl__list_type, PUCCH_PowerControl__list_cond b -> PUCCH_PowerControl__cond (PUCCH_PowerControl__F2 b) /\ PUCCH_PowerControl__F1 (PUCCH_PowerControl__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUCCH_PowerControl__cond, PUCCH_PowerControl__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUCCH_PowerControl__Format : T_Format PUCCH_PowerControl__Type PUCCH_PowerControl__cond :=
 proj2_format PUCCH_PowerControl__cond PUCCH_PowerControl__list_format  PUCCH_PowerControl__F1 PUCCH_PowerControl__F2 PUCCH_PowerControl__helper1 PUCCH_PowerControl__helper2 PUCCH_PowerControl__helper3.

Opaque PUCCH_PowerControl__cond PUCCH_PowerControl__Format.

