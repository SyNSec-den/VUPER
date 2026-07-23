Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Type : Set :=
 | PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__enabled
.
Definition PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__cond := (fun (_ : PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Type) => True).
Lemma PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__nat__helper.

Definition PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F1 t :=
  match t with
  | PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__enabled => 0
  end.
Definition PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F2 n :=
  match n with
  | 0 => PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__enabled
  | _ => PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__enabled
  end.
Lemma PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F1F2 : forall x : PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Type, (PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F1 x <= 0) /\ PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F2 (PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F1 (PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PUSCH_TimeDomainResourceAllocationList.

Opaque PUSCH_TimeDomainResourceAllocationList__cond PUSCH_TimeDomainResourceAllocationList__Format.

Lemma PUSCH_ConfigCommon__msg3_DeltaPreamble__helper1 : (-1 <= 6)%Z.  lia. Qed.
Lemma PUSCH_ConfigCommon__msg3_DeltaPreamble__helper2 : to_bit_sz (Z.to_nat (6 - -1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - -1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_ConfigCommon__msg3_DeltaPreamble__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_ConfigCommon__msg3_DeltaPreamble__Type := Z.
Definition PUSCH_ConfigCommon__msg3_DeltaPreamble__cond := (fun z => (-1 <= z <= 6)%Z).
Lemma PUSCH_ConfigCommon__p0_NominalWithGrant__helper1 : (-202 <= 24)%Z.  lia. Qed.
Lemma PUSCH_ConfigCommon__p0_NominalWithGrant__helper2 : to_bit_sz (Z.to_nat (24 - -202)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (24 - -202))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_ConfigCommon__p0_NominalWithGrant__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_ConfigCommon__p0_NominalWithGrant__Type := Z.
Definition PUSCH_ConfigCommon__p0_NominalWithGrant__cond := (fun z => (-202 <= z <= 24)%Z).
Record PUSCH_ConfigCommon__Type : Set :=
  make__PUSCH_ConfigCommon__Type {
    PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding : option PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Type ;
    PUSCH_ConfigCommon__pusch_TimeDomainAllocationList : option PUSCH_TimeDomainResourceAllocationList__Type ;
    PUSCH_ConfigCommon__msg3_DeltaPreamble : option Z ;
    PUSCH_ConfigCommon__p0_NominalWithGrant : option Z ;
}.
Definition PUSCH_ConfigCommon__root_list : list seq_elem := (
 Opt PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Type PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__cond ::
 Opt PUSCH_TimeDomainResourceAllocationList__Type PUSCH_TimeDomainResourceAllocationList__cond ::
 Opt Z PUSCH_ConfigCommon__msg3_DeltaPreamble__cond ::
 Opt Z PUSCH_ConfigCommon__p0_NominalWithGrant__cond ::
 nil).
Definition PUSCH_ConfigCommon__ext_list : list typ := (
  nil).
Definition PUSCH_ConfigCommon__cond (z : PUSCH_ConfigCommon__Type) := 
(  opt_cond PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__cond (PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding z) /\
  opt_cond PUSCH_TimeDomainResourceAllocationList__cond (PUSCH_ConfigCommon__pusch_TimeDomainAllocationList z) /\
  opt_cond PUSCH_ConfigCommon__msg3_DeltaPreamble__cond (PUSCH_ConfigCommon__msg3_DeltaPreamble z) /\
  opt_cond PUSCH_ConfigCommon__p0_NominalWithGrant__cond (PUSCH_ConfigCommon__p0_NominalWithGrant z) /\
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
Definition PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Format : T_Format PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__nat__Format PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F1 PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F2 PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F1F2 PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__F2F1.

Opaque PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__cond PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Format.

Definition PUSCH_ConfigCommon__msg3_DeltaPreamble__Format : T_Format Z PUSCH_ConfigCommon__msg3_DeltaPreamble__cond :=
 ranged_int_format (-1) (6) PUSCH_ConfigCommon__msg3_DeltaPreamble__helper1 PUSCH_ConfigCommon__msg3_DeltaPreamble__helper2.

Opaque PUSCH_ConfigCommon__msg3_DeltaPreamble__cond PUSCH_ConfigCommon__msg3_DeltaPreamble__Format.

Definition PUSCH_ConfigCommon__p0_NominalWithGrant__Format : T_Format Z PUSCH_ConfigCommon__p0_NominalWithGrant__cond :=
 ranged_int_format (-202) (24) PUSCH_ConfigCommon__p0_NominalWithGrant__helper1 PUSCH_ConfigCommon__p0_NominalWithGrant__helper2.

Opaque PUSCH_ConfigCommon__p0_NominalWithGrant__cond PUSCH_ConfigCommon__p0_NominalWithGrant__Format.


Definition PUSCH_ConfigCommon__root_Format_Type := Eval cbn in seq_format_prod PUSCH_ConfigCommon__root_list.
Definition PUSCH_ConfigCommon__root_Format_list : PUSCH_ConfigCommon__root_Format_Type :=
  (PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding__Format, (PUSCH_TimeDomainResourceAllocationList__Format, (PUSCH_ConfigCommon__msg3_DeltaPreamble__Format, (PUSCH_ConfigCommon__p0_NominalWithGrant__Format, unit_format)))).

Definition PUSCH_ConfigCommon__ext_Format_Type := Eval cbn in get_formats PUSCH_ConfigCommon__ext_list.
Definition PUSCH_ConfigCommon__ext_Format_list : PUSCH_ConfigCommon__ext_Format_Type :=
  unit__Format.

Definition PUSCH_ConfigCommon__list_type : Set := (seq_type PUSCH_ConfigCommon__root_list) * (seq_ext_type PUSCH_ConfigCommon__ext_list).
Definition PUSCH_ConfigCommon__list_cond (z : PUSCH_ConfigCommon__list_type) : Prop :=
        (seq_cond PUSCH_ConfigCommon__root_list (fst z)) /\ (seq_ext_cond PUSCH_ConfigCommon__ext_list (snd z)).
Definition PUSCH_ConfigCommon__list_format : T_Format PUSCH_ConfigCommon__list_type PUSCH_ConfigCommon__list_cond :=
 (* Eval compute in *) seq_ext_format PUSCH_ConfigCommon__root_list PUSCH_ConfigCommon__root_Format_list PUSCH_ConfigCommon__ext_list PUSCH_ConfigCommon__ext_Format_list.

Opaque PUSCH_ConfigCommon__list_format.
Definition PUSCH_ConfigCommon__F1 (z : PUSCH_ConfigCommon__Type) : PUSCH_ConfigCommon__list_type :=
  (((PUSCH_ConfigCommon__groupHoppingEnabledTransformPrecoding z, (PUSCH_ConfigCommon__pusch_TimeDomainAllocationList z, (PUSCH_ConfigCommon__msg3_DeltaPreamble z, (PUSCH_ConfigCommon__p0_NominalWithGrant z, tt))))), (
tt)).
Definition PUSCH_ConfigCommon__F2 (y : PUSCH_ConfigCommon__list_type) : PUSCH_ConfigCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__PUSCH_ConfigCommon__Type j0 j1 j2 j3
  end.
Definition PUSCH_ConfigCommon__helper1 : (forall a : PUSCH_ConfigCommon__Type, PUSCH_ConfigCommon__cond a -> PUSCH_ConfigCommon__list_cond (PUSCH_ConfigCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUSCH_ConfigCommon__helper2 : (forall a : PUSCH_ConfigCommon__Type, PUSCH_ConfigCommon__F2 (PUSCH_ConfigCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUSCH_ConfigCommon__helper3 : (forall b : PUSCH_ConfigCommon__list_type, PUSCH_ConfigCommon__list_cond b -> PUSCH_ConfigCommon__cond (PUSCH_ConfigCommon__F2 b) /\ PUSCH_ConfigCommon__F1 (PUSCH_ConfigCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUSCH_ConfigCommon__cond, PUSCH_ConfigCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUSCH_ConfigCommon__Format : T_Format PUSCH_ConfigCommon__Type PUSCH_ConfigCommon__cond :=
 proj2_format PUSCH_ConfigCommon__cond PUSCH_ConfigCommon__list_format  PUSCH_ConfigCommon__F1 PUSCH_ConfigCommon__F2 PUSCH_ConfigCommon__helper1 PUSCH_ConfigCommon__helper2 PUSCH_ConfigCommon__helper3.

Opaque PUSCH_ConfigCommon__cond PUSCH_ConfigCommon__Format.

