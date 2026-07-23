Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUCCH_ConfigCommon__pucch_ResourceCommon__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma PUCCH_ConfigCommon__pucch_ResourceCommon__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ConfigCommon__pucch_ResourceCommon__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ConfigCommon__pucch_ResourceCommon__Type := Z.
Definition PUCCH_ConfigCommon__pucch_ResourceCommon__cond := (fun z => (0 <= z <= 15)%Z).
Inductive PUCCH_ConfigCommon__pucch_GroupHopping__Type : Set :=
 | PUCCH_ConfigCommon__pucch_GroupHopping__neither
 | PUCCH_ConfigCommon__pucch_GroupHopping__enable
 | PUCCH_ConfigCommon__pucch_GroupHopping__disable
.
Definition PUCCH_ConfigCommon__pucch_GroupHopping__cond := (fun (_ : PUCCH_ConfigCommon__pucch_GroupHopping__Type) => True).
Lemma PUCCH_ConfigCommon__pucch_GroupHopping__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_ConfigCommon__pucch_GroupHopping__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUCCH_ConfigCommon__pucch_GroupHopping__nat__helper.

Definition PUCCH_ConfigCommon__pucch_GroupHopping__F1 t :=
  match t with
  | PUCCH_ConfigCommon__pucch_GroupHopping__neither => 0
  | PUCCH_ConfigCommon__pucch_GroupHopping__enable => 1
  | PUCCH_ConfigCommon__pucch_GroupHopping__disable => 2
  end.
Definition PUCCH_ConfigCommon__pucch_GroupHopping__F2 n :=
  match n with
  | 0 => PUCCH_ConfigCommon__pucch_GroupHopping__neither
  | 1 => PUCCH_ConfigCommon__pucch_GroupHopping__enable
  | 2 => PUCCH_ConfigCommon__pucch_GroupHopping__disable
  | _ => PUCCH_ConfigCommon__pucch_GroupHopping__neither
  end.
Lemma PUCCH_ConfigCommon__pucch_GroupHopping__F1F2 : forall x : PUCCH_ConfigCommon__pucch_GroupHopping__Type, (PUCCH_ConfigCommon__pucch_GroupHopping__F1 x <= 2) /\ PUCCH_ConfigCommon__pucch_GroupHopping__F2 (PUCCH_ConfigCommon__pucch_GroupHopping__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_ConfigCommon__pucch_GroupHopping__F2F1 : forall (y : nat) (H : y <= 2), PUCCH_ConfigCommon__pucch_GroupHopping__F1 (PUCCH_ConfigCommon__pucch_GroupHopping__F2 y) = y. enum_solve H y. Qed.

Lemma PUCCH_ConfigCommon__hoppingId__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma PUCCH_ConfigCommon__hoppingId__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ConfigCommon__hoppingId__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ConfigCommon__hoppingId__Type := Z.
Definition PUCCH_ConfigCommon__hoppingId__cond := (fun z => (0 <= z <= 1023)%Z).
Lemma PUCCH_ConfigCommon__p0_nominal__helper1 : (-202 <= 24)%Z.  lia. Qed.
Lemma PUCCH_ConfigCommon__p0_nominal__helper2 : to_bit_sz (Z.to_nat (24 - -202)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (24 - -202))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ConfigCommon__p0_nominal__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ConfigCommon__p0_nominal__Type := Z.
Definition PUCCH_ConfigCommon__p0_nominal__cond := (fun z => (-202 <= z <= 24)%Z).
Lemma PUCCH_ConfigCommon__ext0O__nrofPRBs__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma PUCCH_ConfigCommon__ext0O__nrofPRBs__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ConfigCommon__ext0O__nrofPRBs__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ConfigCommon__ext0O__nrofPRBs__Type := Z.
Definition PUCCH_ConfigCommon__ext0O__nrofPRBs__cond := (fun z => (1 <= z <= 16)%Z).
Inductive PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Type : Set :=
 | PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__fromLowerEdge
 | PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__fromUpperEdge
.
Definition PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__cond := (fun (_ : PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Type) => True).
Lemma PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__nat__helper.

Definition PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F1 t :=
  match t with
  | PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__fromLowerEdge => 0
  | PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__fromUpperEdge => 1
  end.
Definition PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F2 n :=
  match n with
  | 0 => PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__fromLowerEdge
  | 1 => PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__fromUpperEdge
  | _ => PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__fromLowerEdge
  end.
Lemma PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F1F2 : forall x : PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Type, (PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F1 x <= 1) /\ PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F2 (PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F2F1 : forall (y : nat) (H : y <= 1), PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F1 (PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F2 y) = y. enum_solve H y. Qed.

Lemma PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__Type := Z.
Definition PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__cond := (fun z => (0 <= z <= 15)%Z).
Inductive PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Type : Set :=
 | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n2
 | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n3
 | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n4
 | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n6
 | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n8
 | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n9
 | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n10
 | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n12
.
Definition PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__cond := (fun (_ : PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Type) => True).
Lemma PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__nat__helper.

Definition PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F1 t :=
  match t with
  | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n2 => 0
  | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n3 => 1
  | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n4 => 2
  | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n6 => 3
  | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n8 => 4
  | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n9 => 5
  | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n10 => 6
  | PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n12 => 7
  end.
Definition PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F2 n :=
  match n with
  | 0 => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n2
  | 1 => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n3
  | 2 => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n4
  | 3 => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n6
  | 4 => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n8
  | 5 => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n9
  | 6 => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n10
  | 7 => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n12
  | _ => PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__n2
  end.
Lemma PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F1F2 : forall x : PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Type, (PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F1 x <= 7) /\ PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F2 (PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F2F1 : forall (y : nat) (H : y <= 7), PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F1 (PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F2 y) = y. enum_solve H y. Qed.

Record PUCCH_ConfigCommon__ext0O__Type : Set :=
  make__PUCCH_ConfigCommon__ext0O__Type {
    PUCCH_ConfigCommon__ext0O__nrofPRBs : option Z ;
    PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17 : option PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Type ;
    PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17 : option Z ;
    PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17 : option PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Type ;
}.
Definition PUCCH_ConfigCommon__ext0O__list := (
 Opt Z PUCCH_ConfigCommon__ext0O__nrofPRBs__cond ::
 Opt PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Type PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__cond ::
 Opt Z PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__cond ::
 Opt PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Type PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__cond ::
 nil).
Definition PUCCH_ConfigCommon__ext0O__cond z := 
  opt_cond PUCCH_ConfigCommon__ext0O__nrofPRBs__cond (PUCCH_ConfigCommon__ext0O__nrofPRBs z) /\
  opt_cond PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__cond (PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17 z) /\
  opt_cond PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__cond (PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17 z) /\
  opt_cond PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__cond (PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17 z) /\
  True.

Definition PUCCH_ConfigCommon__ext0__Type := PUCCH_ConfigCommon__ext0O__Type.
Definition PUCCH_ConfigCommon__ext0__cond := PUCCH_ConfigCommon__ext0O__cond.

Record PUCCH_ConfigCommon__Type : Set :=
  make__PUCCH_ConfigCommon__Type {
    PUCCH_ConfigCommon__pucch_ResourceCommon : option Z ;
    PUCCH_ConfigCommon__pucch_GroupHopping : PUCCH_ConfigCommon__pucch_GroupHopping__Type ;
    PUCCH_ConfigCommon__hoppingId : option Z ;
    PUCCH_ConfigCommon__p0_nominal : option Z ;
    PUCCH_ConfigCommon__ext0 : option PUCCH_ConfigCommon__ext0__Type ;
}.
Definition PUCCH_ConfigCommon__root_list : list seq_elem := (
 Opt Z PUCCH_ConfigCommon__pucch_ResourceCommon__cond ::
 Nor PUCCH_ConfigCommon__pucch_GroupHopping__Type PUCCH_ConfigCommon__pucch_GroupHopping__cond ::
 Opt Z PUCCH_ConfigCommon__hoppingId__cond ::
 Opt Z PUCCH_ConfigCommon__p0_nominal__cond ::
 nil).
Definition PUCCH_ConfigCommon__ext_list : list typ := (
  typ_cons PUCCH_ConfigCommon__ext0__Type PUCCH_ConfigCommon__ext0__cond ::
  nil).
Definition PUCCH_ConfigCommon__cond (z : PUCCH_ConfigCommon__Type) := 
(  opt_cond PUCCH_ConfigCommon__pucch_ResourceCommon__cond (PUCCH_ConfigCommon__pucch_ResourceCommon z) /\
  PUCCH_ConfigCommon__pucch_GroupHopping__cond (PUCCH_ConfigCommon__pucch_GroupHopping z) /\
  opt_cond PUCCH_ConfigCommon__hoppingId__cond (PUCCH_ConfigCommon__hoppingId z) /\
  opt_cond PUCCH_ConfigCommon__p0_nominal__cond (PUCCH_ConfigCommon__p0_nominal z) /\
  True) /\ 
(  opt_cond PUCCH_ConfigCommon__ext0__cond (PUCCH_ConfigCommon__ext0 z) /\
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
Definition PUCCH_ConfigCommon__pucch_ResourceCommon__Format : T_Format Z PUCCH_ConfigCommon__pucch_ResourceCommon__cond :=
 ranged_int_format (0) (15) PUCCH_ConfigCommon__pucch_ResourceCommon__helper1 PUCCH_ConfigCommon__pucch_ResourceCommon__helper2.

Opaque PUCCH_ConfigCommon__pucch_ResourceCommon__cond PUCCH_ConfigCommon__pucch_ResourceCommon__Format.

Definition PUCCH_ConfigCommon__pucch_GroupHopping__Format : T_Format PUCCH_ConfigCommon__pucch_GroupHopping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_ConfigCommon__pucch_GroupHopping__nat__Format PUCCH_ConfigCommon__pucch_GroupHopping__F1 PUCCH_ConfigCommon__pucch_GroupHopping__F2 PUCCH_ConfigCommon__pucch_GroupHopping__F1F2 PUCCH_ConfigCommon__pucch_GroupHopping__F2F1.

Opaque PUCCH_ConfigCommon__pucch_GroupHopping__cond PUCCH_ConfigCommon__pucch_GroupHopping__Format.

Definition PUCCH_ConfigCommon__hoppingId__Format : T_Format Z PUCCH_ConfigCommon__hoppingId__cond :=
 ranged_int_format (0) (1023) PUCCH_ConfigCommon__hoppingId__helper1 PUCCH_ConfigCommon__hoppingId__helper2.

Opaque PUCCH_ConfigCommon__hoppingId__cond PUCCH_ConfigCommon__hoppingId__Format.

Definition PUCCH_ConfigCommon__p0_nominal__Format : T_Format Z PUCCH_ConfigCommon__p0_nominal__cond :=
 ranged_int_format (-202) (24) PUCCH_ConfigCommon__p0_nominal__helper1 PUCCH_ConfigCommon__p0_nominal__helper2.

Opaque PUCCH_ConfigCommon__p0_nominal__cond PUCCH_ConfigCommon__p0_nominal__Format.

Definition PUCCH_ConfigCommon__ext0O__nrofPRBs__Format : T_Format Z PUCCH_ConfigCommon__ext0O__nrofPRBs__cond :=
 ranged_int_format (1) (16) PUCCH_ConfigCommon__ext0O__nrofPRBs__helper1 PUCCH_ConfigCommon__ext0O__nrofPRBs__helper2.

Opaque PUCCH_ConfigCommon__ext0O__nrofPRBs__cond PUCCH_ConfigCommon__ext0O__nrofPRBs__Format.

Definition PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Format : T_Format PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__nat__Format PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F1 PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F2 PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F1F2 PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__F2F1.

Opaque PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__cond PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Format.

Definition PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__Format : T_Format Z PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__cond :=
 ranged_int_format (0) (15) PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__helper1 PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__helper2.

Opaque PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__cond PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__Format.

Definition PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Format : T_Format PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__nat__Format PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F1 PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F2 PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F1F2 PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__F2F1.

Opaque PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__cond PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Format.


Definition PUCCH_ConfigCommon__ext0O__Format_Type := Eval cbn in seq_format_prod PUCCH_ConfigCommon__ext0O__list.
Definition PUCCH_ConfigCommon__ext0O__Format_list : PUCCH_ConfigCommon__ext0O__Format_Type :=
  (PUCCH_ConfigCommon__ext0O__nrofPRBs__Format, (PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17__Format, (PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17__Format, (PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17__Format, unit_format)))).
Definition PUCCH_ConfigCommon__ext0O__list__Format := (*Eval compute in *) seq_format PUCCH_ConfigCommon__ext0O__list PUCCH_ConfigCommon__ext0O__Format_list.
Definition PUCCH_ConfigCommon__ext0O__F1 z :=
  (PUCCH_ConfigCommon__ext0O__nrofPRBs z, (PUCCH_ConfigCommon__ext0O__intra_SlotFH_r17 z, (PUCCH_ConfigCommon__ext0O__pucch_ResourceCommonRedCap_r17 z, (PUCCH_ConfigCommon__ext0O__additionalPRBOffset_r17 z, tt)))).
Definition PUCCH_ConfigCommon__ext0O__F2 (y : seq_type PUCCH_ConfigCommon__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PUCCH_ConfigCommon__ext0O__Type i0 i1 i2 i3
  end.
Lemma PUCCH_ConfigCommon__ext0O__F1F2_cond (z : PUCCH_ConfigCommon__ext0O__Type)
  : PUCCH_ConfigCommon__ext0O__cond z ->
  (seq_cond PUCCH_ConfigCommon__ext0O__list (PUCCH_ConfigCommon__ext0O__F1 z)).
intro H. unfold PUCCH_ConfigCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma PUCCH_ConfigCommon__ext0O__F1F2_cond2 (z : PUCCH_ConfigCommon__ext0O__Type)
 : PUCCH_ConfigCommon__ext0O__F2 (PUCCH_ConfigCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_ConfigCommon__ext0O__F2F1_cond (y : seq_type PUCCH_ConfigCommon__ext0O__list)
  : seq_cond PUCCH_ConfigCommon__ext0O__list y ->
 (PUCCH_ConfigCommon__ext0O__cond (PUCCH_ConfigCommon__ext0O__F2 y)) /\  PUCCH_ConfigCommon__ext0O__F1 (PUCCH_ConfigCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_ConfigCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUCCH_ConfigCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_ConfigCommon__ext0O__Format : T_Format PUCCH_ConfigCommon__ext0O__Type PUCCH_ConfigCommon__ext0O__cond :=
        proj2_format  PUCCH_ConfigCommon__ext0O__cond PUCCH_ConfigCommon__ext0O__list__Format
    PUCCH_ConfigCommon__ext0O__F1 PUCCH_ConfigCommon__ext0O__F2 PUCCH_ConfigCommon__ext0O__F1F2_cond  PUCCH_ConfigCommon__ext0O__F1F2_cond2 PUCCH_ConfigCommon__ext0O__F2F1_cond.
Opaque PUCCH_ConfigCommon__ext0O__cond PUCCH_ConfigCommon__ext0O__Format.

Definition PUCCH_ConfigCommon__ext0__check_all_none (b : PUCCH_ConfigCommon__ext0O__Type) : bool :=
match b with 
  | make__PUCCH_ConfigCommon__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition PUCCH_ConfigCommon__ext0__Format : T_Format PUCCH_ConfigCommon__ext0__Type PUCCH_ConfigCommon__ext0__cond :=
  restrict_add_format PUCCH_ConfigCommon__ext0__check_all_none PUCCH_ConfigCommon__ext0O__Format.

Opaque PUCCH_ConfigCommon__ext0__cond PUCCH_ConfigCommon__ext0__Format.


Definition PUCCH_ConfigCommon__root_Format_Type := Eval cbn in seq_format_prod PUCCH_ConfigCommon__root_list.
Definition PUCCH_ConfigCommon__root_Format_list : PUCCH_ConfigCommon__root_Format_Type :=
  (PUCCH_ConfigCommon__pucch_ResourceCommon__Format, (PUCCH_ConfigCommon__pucch_GroupHopping__Format, (PUCCH_ConfigCommon__hoppingId__Format, (PUCCH_ConfigCommon__p0_nominal__Format, unit_format)))).

Definition PUCCH_ConfigCommon__ext_Format_Type := Eval cbn in get_formats PUCCH_ConfigCommon__ext_list.
Definition PUCCH_ConfigCommon__ext_Format_list : PUCCH_ConfigCommon__ext_Format_Type :=
  (PUCCH_ConfigCommon__ext0__Format, unit__Format).

Definition PUCCH_ConfigCommon__list_type : Set := (seq_type PUCCH_ConfigCommon__root_list) * (seq_ext_type PUCCH_ConfigCommon__ext_list).
Definition PUCCH_ConfigCommon__list_cond (z : PUCCH_ConfigCommon__list_type) : Prop :=
        (seq_cond PUCCH_ConfigCommon__root_list (fst z)) /\ (seq_ext_cond PUCCH_ConfigCommon__ext_list (snd z)).
Definition PUCCH_ConfigCommon__list_format : T_Format PUCCH_ConfigCommon__list_type PUCCH_ConfigCommon__list_cond :=
 (* Eval compute in *) seq_ext_format PUCCH_ConfigCommon__root_list PUCCH_ConfigCommon__root_Format_list PUCCH_ConfigCommon__ext_list PUCCH_ConfigCommon__ext_Format_list.

Opaque PUCCH_ConfigCommon__list_format.
Definition PUCCH_ConfigCommon__F1 (z : PUCCH_ConfigCommon__Type) : PUCCH_ConfigCommon__list_type :=
  (((PUCCH_ConfigCommon__pucch_ResourceCommon z, (PUCCH_ConfigCommon__pucch_GroupHopping z, (PUCCH_ConfigCommon__hoppingId z, (PUCCH_ConfigCommon__p0_nominal z, tt))))), (
(PUCCH_ConfigCommon__ext0 z, tt))).
Definition PUCCH_ConfigCommon__F2 (y : PUCCH_ConfigCommon__list_type) : PUCCH_ConfigCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__PUCCH_ConfigCommon__Type j0 j1 j2 j3 i0
  end.
Definition PUCCH_ConfigCommon__helper1 : (forall a : PUCCH_ConfigCommon__Type, PUCCH_ConfigCommon__cond a -> PUCCH_ConfigCommon__list_cond (PUCCH_ConfigCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUCCH_ConfigCommon__helper2 : (forall a : PUCCH_ConfigCommon__Type, PUCCH_ConfigCommon__F2 (PUCCH_ConfigCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUCCH_ConfigCommon__helper3 : (forall b : PUCCH_ConfigCommon__list_type, PUCCH_ConfigCommon__list_cond b -> PUCCH_ConfigCommon__cond (PUCCH_ConfigCommon__F2 b) /\ PUCCH_ConfigCommon__F1 (PUCCH_ConfigCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUCCH_ConfigCommon__cond, PUCCH_ConfigCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUCCH_ConfigCommon__Format : T_Format PUCCH_ConfigCommon__Type PUCCH_ConfigCommon__cond :=
 proj2_format PUCCH_ConfigCommon__cond PUCCH_ConfigCommon__list_format  PUCCH_ConfigCommon__F1 PUCCH_ConfigCommon__F2 PUCCH_ConfigCommon__helper1 PUCCH_ConfigCommon__helper2 PUCCH_ConfigCommon__helper3.

Opaque PUCCH_ConfigCommon__cond PUCCH_ConfigCommon__Format.

