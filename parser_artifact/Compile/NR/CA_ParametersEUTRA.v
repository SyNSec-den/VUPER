Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CA_ParametersEUTRA__multipleTimingAdvance__Type : Set :=
 | CA_ParametersEUTRA__multipleTimingAdvance__supported
.
Definition CA_ParametersEUTRA__multipleTimingAdvance__cond := (fun (_ : CA_ParametersEUTRA__multipleTimingAdvance__Type) => True).
Lemma CA_ParametersEUTRA__multipleTimingAdvance__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersEUTRA__multipleTimingAdvance__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersEUTRA__multipleTimingAdvance__nat__helper.

Definition CA_ParametersEUTRA__multipleTimingAdvance__F1 t :=
  match t with
  | CA_ParametersEUTRA__multipleTimingAdvance__supported => 0
  end.
Definition CA_ParametersEUTRA__multipleTimingAdvance__F2 n :=
  match n with
  | 0 => CA_ParametersEUTRA__multipleTimingAdvance__supported
  | _ => CA_ParametersEUTRA__multipleTimingAdvance__supported
  end.
Lemma CA_ParametersEUTRA__multipleTimingAdvance__F1F2 : forall x : CA_ParametersEUTRA__multipleTimingAdvance__Type, (CA_ParametersEUTRA__multipleTimingAdvance__F1 x <= 0) /\ CA_ParametersEUTRA__multipleTimingAdvance__F2 (CA_ParametersEUTRA__multipleTimingAdvance__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersEUTRA__multipleTimingAdvance__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersEUTRA__multipleTimingAdvance__F1 (CA_ParametersEUTRA__multipleTimingAdvance__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersEUTRA__simultaneousRx_Tx__Type : Set :=
 | CA_ParametersEUTRA__simultaneousRx_Tx__supported
.
Definition CA_ParametersEUTRA__simultaneousRx_Tx__cond := (fun (_ : CA_ParametersEUTRA__simultaneousRx_Tx__Type) => True).
Lemma CA_ParametersEUTRA__simultaneousRx_Tx__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersEUTRA__simultaneousRx_Tx__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersEUTRA__simultaneousRx_Tx__nat__helper.

Definition CA_ParametersEUTRA__simultaneousRx_Tx__F1 t :=
  match t with
  | CA_ParametersEUTRA__simultaneousRx_Tx__supported => 0
  end.
Definition CA_ParametersEUTRA__simultaneousRx_Tx__F2 n :=
  match n with
  | 0 => CA_ParametersEUTRA__simultaneousRx_Tx__supported
  | _ => CA_ParametersEUTRA__simultaneousRx_Tx__supported
  end.
Lemma CA_ParametersEUTRA__simultaneousRx_Tx__F1F2 : forall x : CA_ParametersEUTRA__simultaneousRx_Tx__Type, (CA_ParametersEUTRA__simultaneousRx_Tx__F1 x <= 0) /\ CA_ParametersEUTRA__simultaneousRx_Tx__F2 (CA_ParametersEUTRA__simultaneousRx_Tx__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersEUTRA__simultaneousRx_Tx__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersEUTRA__simultaneousRx_Tx__F1 (CA_ParametersEUTRA__simultaneousRx_Tx__F2 y) = y. enum_solve H y. Qed.

Lemma CA_ParametersEUTRA__supportedNAICS_2CRS_AP__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma CA_ParametersEUTRA__supportedNAICS_2CRS_AP__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersEUTRA__supportedNAICS_2CRS_AP__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersEUTRA__supportedNAICS_2CRS_AP__Type := bit_string.
Definition CA_ParametersEUTRA__supportedNAICS_2CRS_AP__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 8)%Z /\ bit_string_len_prop (fst z) (snd z)).
Inductive CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Type : Set :=
 | CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__supported
.
Definition CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__cond := (fun (_ : CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Type) => True).
Lemma CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__nat__helper.

Definition CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F1 t :=
  match t with
  | CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__supported => 0
  end.
Definition CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F2 n :=
  match n with
  | 0 => CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__supported
  | _ => CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__supported
  end.
Lemma CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F1F2 : forall x : CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Type, (CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F1 x <= 0) /\ CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F2 (CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F1 (CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersEUTRA__ue_CA_PowerClass_N__Type : Set :=
 | CA_ParametersEUTRA__ue_CA_PowerClass_N__class2
.
Definition CA_ParametersEUTRA__ue_CA_PowerClass_N__cond := (fun (_ : CA_ParametersEUTRA__ue_CA_PowerClass_N__Type) => True).
Lemma CA_ParametersEUTRA__ue_CA_PowerClass_N__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersEUTRA__ue_CA_PowerClass_N__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersEUTRA__ue_CA_PowerClass_N__nat__helper.

Definition CA_ParametersEUTRA__ue_CA_PowerClass_N__F1 t :=
  match t with
  | CA_ParametersEUTRA__ue_CA_PowerClass_N__class2 => 0
  end.
Definition CA_ParametersEUTRA__ue_CA_PowerClass_N__F2 n :=
  match n with
  | 0 => CA_ParametersEUTRA__ue_CA_PowerClass_N__class2
  | _ => CA_ParametersEUTRA__ue_CA_PowerClass_N__class2
  end.
Lemma CA_ParametersEUTRA__ue_CA_PowerClass_N__F1F2 : forall x : CA_ParametersEUTRA__ue_CA_PowerClass_N__Type, (CA_ParametersEUTRA__ue_CA_PowerClass_N__F1 x <= 0) /\ CA_ParametersEUTRA__ue_CA_PowerClass_N__F2 (CA_ParametersEUTRA__ue_CA_PowerClass_N__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersEUTRA__ue_CA_PowerClass_N__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersEUTRA__ue_CA_PowerClass_N__F1 (CA_ParametersEUTRA__ue_CA_PowerClass_N__F2 y) = y. enum_solve H y. Qed.

Lemma CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__helper1 : (0 <= 1 <= 32)%Z.  lia. Qed.
Lemma CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__Type := bit_string.
Definition CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 32)%Z /\ bit_string_len_prop (fst z) (snd z)).
Record CA_ParametersEUTRA__Type : Set :=
  make__CA_ParametersEUTRA__Type {
    CA_ParametersEUTRA__multipleTimingAdvance : option CA_ParametersEUTRA__multipleTimingAdvance__Type ;
    CA_ParametersEUTRA__simultaneousRx_Tx : option CA_ParametersEUTRA__simultaneousRx_Tx__Type ;
    CA_ParametersEUTRA__supportedNAICS_2CRS_AP : option CA_ParametersEUTRA__supportedNAICS_2CRS_AP__Type ;
    CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq : option CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Type ;
    CA_ParametersEUTRA__ue_CA_PowerClass_N : option CA_ParametersEUTRA__ue_CA_PowerClass_N__Type ;
    CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530 : option CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__Type ;
}.
Definition CA_ParametersEUTRA__root_list : list seq_elem := (
 Opt CA_ParametersEUTRA__multipleTimingAdvance__Type CA_ParametersEUTRA__multipleTimingAdvance__cond ::
 Opt CA_ParametersEUTRA__simultaneousRx_Tx__Type CA_ParametersEUTRA__simultaneousRx_Tx__cond ::
 Opt CA_ParametersEUTRA__supportedNAICS_2CRS_AP__Type CA_ParametersEUTRA__supportedNAICS_2CRS_AP__cond ::
 Opt CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Type CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__cond ::
 Opt CA_ParametersEUTRA__ue_CA_PowerClass_N__Type CA_ParametersEUTRA__ue_CA_PowerClass_N__cond ::
 Opt CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__Type CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__cond ::
 nil).
Definition CA_ParametersEUTRA__ext_list : list typ := (
  nil).
Definition CA_ParametersEUTRA__cond (z : CA_ParametersEUTRA__Type) := 
(  opt_cond CA_ParametersEUTRA__multipleTimingAdvance__cond (CA_ParametersEUTRA__multipleTimingAdvance z) /\
  opt_cond CA_ParametersEUTRA__simultaneousRx_Tx__cond (CA_ParametersEUTRA__simultaneousRx_Tx z) /\
  opt_cond CA_ParametersEUTRA__supportedNAICS_2CRS_AP__cond (CA_ParametersEUTRA__supportedNAICS_2CRS_AP z) /\
  opt_cond CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__cond (CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq z) /\
  opt_cond CA_ParametersEUTRA__ue_CA_PowerClass_N__cond (CA_ParametersEUTRA__ue_CA_PowerClass_N z) /\
  opt_cond CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__cond (CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530 z) /\
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
Definition CA_ParametersEUTRA__multipleTimingAdvance__Format : T_Format CA_ParametersEUTRA__multipleTimingAdvance__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersEUTRA__multipleTimingAdvance__nat__Format CA_ParametersEUTRA__multipleTimingAdvance__F1 CA_ParametersEUTRA__multipleTimingAdvance__F2 CA_ParametersEUTRA__multipleTimingAdvance__F1F2 CA_ParametersEUTRA__multipleTimingAdvance__F2F1.

Opaque CA_ParametersEUTRA__multipleTimingAdvance__cond CA_ParametersEUTRA__multipleTimingAdvance__Format.

Definition CA_ParametersEUTRA__simultaneousRx_Tx__Format : T_Format CA_ParametersEUTRA__simultaneousRx_Tx__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersEUTRA__simultaneousRx_Tx__nat__Format CA_ParametersEUTRA__simultaneousRx_Tx__F1 CA_ParametersEUTRA__simultaneousRx_Tx__F2 CA_ParametersEUTRA__simultaneousRx_Tx__F1F2 CA_ParametersEUTRA__simultaneousRx_Tx__F2F1.

Opaque CA_ParametersEUTRA__simultaneousRx_Tx__cond CA_ParametersEUTRA__simultaneousRx_Tx__Format.

Definition CA_ParametersEUTRA__supportedNAICS_2CRS_AP__Format : T_Format CA_ParametersEUTRA__supportedNAICS_2CRS_AP__Type CA_ParametersEUTRA__supportedNAICS_2CRS_AP__cond := (* Eval compute in *) bit_string_ranged_format 1 8 CA_ParametersEUTRA__supportedNAICS_2CRS_AP__helper1 CA_ParametersEUTRA__supportedNAICS_2CRS_AP__helper2.
Opaque CA_ParametersEUTRA__supportedNAICS_2CRS_AP__cond CA_ParametersEUTRA__supportedNAICS_2CRS_AP__Format.

Definition CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Format : T_Format CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__nat__Format CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F1 CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F2 CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F1F2 CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__F2F1.

Opaque CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__cond CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Format.

Definition CA_ParametersEUTRA__ue_CA_PowerClass_N__Format : T_Format CA_ParametersEUTRA__ue_CA_PowerClass_N__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersEUTRA__ue_CA_PowerClass_N__nat__Format CA_ParametersEUTRA__ue_CA_PowerClass_N__F1 CA_ParametersEUTRA__ue_CA_PowerClass_N__F2 CA_ParametersEUTRA__ue_CA_PowerClass_N__F1F2 CA_ParametersEUTRA__ue_CA_PowerClass_N__F2F1.

Opaque CA_ParametersEUTRA__ue_CA_PowerClass_N__cond CA_ParametersEUTRA__ue_CA_PowerClass_N__Format.

Definition CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__Format : T_Format CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__Type CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__cond := (* Eval compute in *) bit_string_ranged_format 1 32 CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__helper1 CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__helper2.
Opaque CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__cond CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__Format.


Definition CA_ParametersEUTRA__root_Format_Type := Eval cbn in seq_format_prod CA_ParametersEUTRA__root_list.
Definition CA_ParametersEUTRA__root_Format_list : CA_ParametersEUTRA__root_Format_Type :=
  (CA_ParametersEUTRA__multipleTimingAdvance__Format, (CA_ParametersEUTRA__simultaneousRx_Tx__Format, (CA_ParametersEUTRA__supportedNAICS_2CRS_AP__Format, (CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq__Format, (CA_ParametersEUTRA__ue_CA_PowerClass_N__Format, (CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530__Format, unit_format)))))).

Definition CA_ParametersEUTRA__ext_Format_Type := Eval cbn in get_formats CA_ParametersEUTRA__ext_list.
Definition CA_ParametersEUTRA__ext_Format_list : CA_ParametersEUTRA__ext_Format_Type :=
  unit__Format.

Definition CA_ParametersEUTRA__list_type : Set := (seq_type CA_ParametersEUTRA__root_list) * (seq_ext_type CA_ParametersEUTRA__ext_list).
Definition CA_ParametersEUTRA__list_cond (z : CA_ParametersEUTRA__list_type) : Prop :=
        (seq_cond CA_ParametersEUTRA__root_list (fst z)) /\ (seq_ext_cond CA_ParametersEUTRA__ext_list (snd z)).
Definition CA_ParametersEUTRA__list_format : T_Format CA_ParametersEUTRA__list_type CA_ParametersEUTRA__list_cond :=
 (* Eval compute in *) seq_ext_format CA_ParametersEUTRA__root_list CA_ParametersEUTRA__root_Format_list CA_ParametersEUTRA__ext_list CA_ParametersEUTRA__ext_Format_list.

Opaque CA_ParametersEUTRA__list_format.
Definition CA_ParametersEUTRA__F1 (z : CA_ParametersEUTRA__Type) : CA_ParametersEUTRA__list_type :=
  (((CA_ParametersEUTRA__multipleTimingAdvance z, (CA_ParametersEUTRA__simultaneousRx_Tx z, (CA_ParametersEUTRA__supportedNAICS_2CRS_AP z, (CA_ParametersEUTRA__additionalRx_Tx_PerformanceReq z, (CA_ParametersEUTRA__ue_CA_PowerClass_N z, (CA_ParametersEUTRA__supportedBandwidthCombinationSetEUTRA_v1530 z, tt))))))), (
tt)).
Definition CA_ParametersEUTRA__F2 (y : CA_ParametersEUTRA__list_type) : CA_ParametersEUTRA__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__CA_ParametersEUTRA__Type j0 j1 j2 j3 j4 j5
  end.
Definition CA_ParametersEUTRA__helper1 : (forall a : CA_ParametersEUTRA__Type, CA_ParametersEUTRA__cond a -> CA_ParametersEUTRA__list_cond (CA_ParametersEUTRA__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CA_ParametersEUTRA__helper2 : (forall a : CA_ParametersEUTRA__Type, CA_ParametersEUTRA__F2 (CA_ParametersEUTRA__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CA_ParametersEUTRA__helper3 : (forall b : CA_ParametersEUTRA__list_type, CA_ParametersEUTRA__list_cond b -> CA_ParametersEUTRA__cond (CA_ParametersEUTRA__F2 b) /\ CA_ParametersEUTRA__F1 (CA_ParametersEUTRA__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CA_ParametersEUTRA__cond, CA_ParametersEUTRA__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CA_ParametersEUTRA__Format : T_Format CA_ParametersEUTRA__Type CA_ParametersEUTRA__cond :=
 proj2_format CA_ParametersEUTRA__cond CA_ParametersEUTRA__list_format  CA_ParametersEUTRA__F1 CA_ParametersEUTRA__F2 CA_ParametersEUTRA__helper1 CA_ParametersEUTRA__helper2 CA_ParametersEUTRA__helper3.

Opaque CA_ParametersEUTRA__cond CA_ParametersEUTRA__Format.

