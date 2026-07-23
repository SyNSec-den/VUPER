Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.MultiFrequencyBandListNR.

Opaque MultiFrequencyBandListNR__cond MultiFrequencyBandListNR__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.SCS_SpecificCarrier.

Opaque SCS_SpecificCarrier__cond SCS_SpecificCarrier__Format.

Definition FrequencyInfoDL__scs_SpecificCarrierList__Type := list SCS_SpecificCarrier__Type.

Lemma FrequencyInfoDL__scs_SpecificCarrierList__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma FrequencyInfoDL__scs_SpecificCarrierList__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FrequencyInfoDL__scs_SpecificCarrierList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FrequencyInfoDL__scs_SpecificCarrierList__cond (z : FrequencyInfoDL__scs_SpecificCarrierList__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SCS_SpecificCarrier__cond z) .

Record FrequencyInfoDL__Type : Set :=
  make__FrequencyInfoDL__Type {
    FrequencyInfoDL__absoluteFrequencySSB : option ARFCN_ValueNR__Type ;
    FrequencyInfoDL__frequencyBandList : MultiFrequencyBandListNR__Type ;
    FrequencyInfoDL__absoluteFrequencyPointA : ARFCN_ValueNR__Type ;
    FrequencyInfoDL__scs_SpecificCarrierList : FrequencyInfoDL__scs_SpecificCarrierList__Type ;
}.
Definition FrequencyInfoDL__root_list : list seq_elem := (
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor MultiFrequencyBandListNR__Type MultiFrequencyBandListNR__cond ::
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor FrequencyInfoDL__scs_SpecificCarrierList__Type FrequencyInfoDL__scs_SpecificCarrierList__cond ::
 nil).
Definition FrequencyInfoDL__ext_list : list typ := (
  nil).
Definition FrequencyInfoDL__cond (z : FrequencyInfoDL__Type) := 
(  opt_cond ARFCN_ValueNR__cond (FrequencyInfoDL__absoluteFrequencySSB z) /\
  MultiFrequencyBandListNR__cond (FrequencyInfoDL__frequencyBandList z) /\
  ARFCN_ValueNR__cond (FrequencyInfoDL__absoluteFrequencyPointA z) /\
  FrequencyInfoDL__scs_SpecificCarrierList__cond (FrequencyInfoDL__scs_SpecificCarrierList z) /\
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
Definition FrequencyInfoDL__scs_SpecificCarrierList__Format : T_Format FrequencyInfoDL__scs_SpecificCarrierList__Type FrequencyInfoDL__scs_SpecificCarrierList__cond := seq_of_format SCS_SpecificCarrier__Format 1 maxSCSs FrequencyInfoDL__scs_SpecificCarrierList__helper1 FrequencyInfoDL__scs_SpecificCarrierList__helper2.

Opaque FrequencyInfoDL__scs_SpecificCarrierList__cond FrequencyInfoDL__scs_SpecificCarrierList__Format.


Definition FrequencyInfoDL__root_Format_Type := Eval cbn in seq_format_prod FrequencyInfoDL__root_list.
Definition FrequencyInfoDL__root_Format_list : FrequencyInfoDL__root_Format_Type :=
  (ARFCN_ValueNR__Format, (MultiFrequencyBandListNR__Format, (ARFCN_ValueNR__Format, (FrequencyInfoDL__scs_SpecificCarrierList__Format, unit_format)))).

Definition FrequencyInfoDL__ext_Format_Type := Eval cbn in get_formats FrequencyInfoDL__ext_list.
Definition FrequencyInfoDL__ext_Format_list : FrequencyInfoDL__ext_Format_Type :=
  unit__Format.

Definition FrequencyInfoDL__list_type : Set := (seq_type FrequencyInfoDL__root_list) * (seq_ext_type FrequencyInfoDL__ext_list).
Definition FrequencyInfoDL__list_cond (z : FrequencyInfoDL__list_type) : Prop :=
        (seq_cond FrequencyInfoDL__root_list (fst z)) /\ (seq_ext_cond FrequencyInfoDL__ext_list (snd z)).
Definition FrequencyInfoDL__list_format : T_Format FrequencyInfoDL__list_type FrequencyInfoDL__list_cond :=
 (* Eval compute in *) seq_ext_format FrequencyInfoDL__root_list FrequencyInfoDL__root_Format_list FrequencyInfoDL__ext_list FrequencyInfoDL__ext_Format_list.

Opaque FrequencyInfoDL__list_format.
Definition FrequencyInfoDL__F1 (z : FrequencyInfoDL__Type) : FrequencyInfoDL__list_type :=
  (((FrequencyInfoDL__absoluteFrequencySSB z, (FrequencyInfoDL__frequencyBandList z, (FrequencyInfoDL__absoluteFrequencyPointA z, (FrequencyInfoDL__scs_SpecificCarrierList z, tt))))), (
tt)).
Definition FrequencyInfoDL__F2 (y : FrequencyInfoDL__list_type) : FrequencyInfoDL__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__FrequencyInfoDL__Type j0 j1 j2 j3
  end.
Definition FrequencyInfoDL__helper1 : (forall a : FrequencyInfoDL__Type, FrequencyInfoDL__cond a -> FrequencyInfoDL__list_cond (FrequencyInfoDL__F1 a)).
                     intros. destruct a. auto. Qed.
Definition FrequencyInfoDL__helper2 : (forall a : FrequencyInfoDL__Type, FrequencyInfoDL__F2 (FrequencyInfoDL__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition FrequencyInfoDL__helper3 : (forall b : FrequencyInfoDL__list_type, FrequencyInfoDL__list_cond b -> FrequencyInfoDL__cond (FrequencyInfoDL__F2 b) /\ FrequencyInfoDL__F1 (FrequencyInfoDL__F2 b) = b).
                     intros. destruct b as [y y1]. unfold FrequencyInfoDL__cond, FrequencyInfoDL__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition FrequencyInfoDL__Format : T_Format FrequencyInfoDL__Type FrequencyInfoDL__cond :=
 proj2_format FrequencyInfoDL__cond FrequencyInfoDL__list_format  FrequencyInfoDL__F1 FrequencyInfoDL__F2 FrequencyInfoDL__helper1 FrequencyInfoDL__helper2 FrequencyInfoDL__helper3.

Opaque FrequencyInfoDL__cond FrequencyInfoDL__Format.

