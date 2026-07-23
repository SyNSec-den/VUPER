Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandIndicatorEUTRA.

Opaque FreqBandIndicatorEUTRA__cond FreqBandIndicatorEUTRA__Format.

Definition EUTRA_Parameters__supportedBandListEUTRA__Type := list FreqBandIndicatorEUTRA__Type.

Lemma EUTRA_Parameters__supportedBandListEUTRA__helper1 : (0 <= 1 <= maxBandsEUTRA)%Z. unfold maxBandsEUTRA.
 lia. Qed.
Lemma EUTRA_Parameters__supportedBandListEUTRA__helper2 : to_bit_sz (Z.to_nat (maxBandsEUTRA - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBandsEUTRA - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EUTRA_Parameters__supportedBandListEUTRA__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EUTRA_Parameters__supportedBandListEUTRA__cond (z : EUTRA_Parameters__supportedBandListEUTRA__Type) :=  (1 <= Z.of_nat (length z) <= maxBandsEUTRA)%Z /\ (list_and FreqBandIndicatorEUTRA__cond z) .

Require Import NR.EUTRA_ParametersCommon.

Opaque EUTRA_ParametersCommon__cond EUTRA_ParametersCommon__Format.

Require Import NR.EUTRA_ParametersXDD_Diff.

Opaque EUTRA_ParametersXDD_Diff__cond EUTRA_ParametersXDD_Diff__Format.

Record EUTRA_Parameters__Type : Set :=
  make__EUTRA_Parameters__Type {
    EUTRA_Parameters__supportedBandListEUTRA : EUTRA_Parameters__supportedBandListEUTRA__Type ;
    EUTRA_Parameters__eutra_ParametersCommon : option EUTRA_ParametersCommon__Type ;
    EUTRA_Parameters__eutra_ParametersXDD_Diff : option EUTRA_ParametersXDD_Diff__Type ;
}.
Definition EUTRA_Parameters__root_list : list seq_elem := (
 Nor EUTRA_Parameters__supportedBandListEUTRA__Type EUTRA_Parameters__supportedBandListEUTRA__cond ::
 Opt EUTRA_ParametersCommon__Type EUTRA_ParametersCommon__cond ::
 Opt EUTRA_ParametersXDD_Diff__Type EUTRA_ParametersXDD_Diff__cond ::
 nil).
Definition EUTRA_Parameters__ext_list : list typ := (
  nil).
Definition EUTRA_Parameters__cond (z : EUTRA_Parameters__Type) := 
(  EUTRA_Parameters__supportedBandListEUTRA__cond (EUTRA_Parameters__supportedBandListEUTRA z) /\
  opt_cond EUTRA_ParametersCommon__cond (EUTRA_Parameters__eutra_ParametersCommon z) /\
  opt_cond EUTRA_ParametersXDD_Diff__cond (EUTRA_Parameters__eutra_ParametersXDD_Diff z) /\
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
Definition EUTRA_Parameters__supportedBandListEUTRA__Format : T_Format EUTRA_Parameters__supportedBandListEUTRA__Type EUTRA_Parameters__supportedBandListEUTRA__cond := seq_of_format FreqBandIndicatorEUTRA__Format 1 maxBandsEUTRA EUTRA_Parameters__supportedBandListEUTRA__helper1 EUTRA_Parameters__supportedBandListEUTRA__helper2.

Opaque EUTRA_Parameters__supportedBandListEUTRA__cond EUTRA_Parameters__supportedBandListEUTRA__Format.


Definition EUTRA_Parameters__root_Format_Type := Eval cbn in seq_format_prod EUTRA_Parameters__root_list.
Definition EUTRA_Parameters__root_Format_list : EUTRA_Parameters__root_Format_Type :=
  (EUTRA_Parameters__supportedBandListEUTRA__Format, (EUTRA_ParametersCommon__Format, (EUTRA_ParametersXDD_Diff__Format, unit_format))).

Definition EUTRA_Parameters__ext_Format_Type := Eval cbn in get_formats EUTRA_Parameters__ext_list.
Definition EUTRA_Parameters__ext_Format_list : EUTRA_Parameters__ext_Format_Type :=
  unit__Format.

Definition EUTRA_Parameters__list_type : Set := (seq_type EUTRA_Parameters__root_list) * (seq_ext_type EUTRA_Parameters__ext_list).
Definition EUTRA_Parameters__list_cond (z : EUTRA_Parameters__list_type) : Prop :=
        (seq_cond EUTRA_Parameters__root_list (fst z)) /\ (seq_ext_cond EUTRA_Parameters__ext_list (snd z)).
Definition EUTRA_Parameters__list_format : T_Format EUTRA_Parameters__list_type EUTRA_Parameters__list_cond :=
 (* Eval compute in *) seq_ext_format EUTRA_Parameters__root_list EUTRA_Parameters__root_Format_list EUTRA_Parameters__ext_list EUTRA_Parameters__ext_Format_list.

Opaque EUTRA_Parameters__list_format.
Definition EUTRA_Parameters__F1 (z : EUTRA_Parameters__Type) : EUTRA_Parameters__list_type :=
  (((EUTRA_Parameters__supportedBandListEUTRA z, (EUTRA_Parameters__eutra_ParametersCommon z, (EUTRA_Parameters__eutra_ParametersXDD_Diff z, tt)))), (
tt)).
Definition EUTRA_Parameters__F2 (y : EUTRA_Parameters__list_type) : EUTRA_Parameters__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__EUTRA_Parameters__Type j0 j1 j2
  end.
Definition EUTRA_Parameters__helper1 : (forall a : EUTRA_Parameters__Type, EUTRA_Parameters__cond a -> EUTRA_Parameters__list_cond (EUTRA_Parameters__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EUTRA_Parameters__helper2 : (forall a : EUTRA_Parameters__Type, EUTRA_Parameters__F2 (EUTRA_Parameters__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EUTRA_Parameters__helper3 : (forall b : EUTRA_Parameters__list_type, EUTRA_Parameters__list_cond b -> EUTRA_Parameters__cond (EUTRA_Parameters__F2 b) /\ EUTRA_Parameters__F1 (EUTRA_Parameters__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EUTRA_Parameters__cond, EUTRA_Parameters__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EUTRA_Parameters__Format : T_Format EUTRA_Parameters__Type EUTRA_Parameters__cond :=
 proj2_format EUTRA_Parameters__cond EUTRA_Parameters__list_format  EUTRA_Parameters__F1 EUTRA_Parameters__F2 EUTRA_Parameters__helper1 EUTRA_Parameters__helper2 EUTRA_Parameters__helper3.

Opaque EUTRA_Parameters__cond EUTRA_Parameters__Format.

