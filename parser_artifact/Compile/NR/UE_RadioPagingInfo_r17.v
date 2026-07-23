Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Definition UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__Type := list FreqBandIndicatorNR__Type.

Lemma UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__helper1 : (0 <= 1 <= maxBands)%Z. unfold maxBands.
 lia. Qed.
Lemma UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__helper2 : to_bit_sz (Z.to_nat (maxBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__cond (z : UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxBands)%Z /\ (list_and FreqBandIndicatorNR__cond z) .

Record UE_RadioPagingInfo_r17__Type : Set :=
  make__UE_RadioPagingInfo_r17__Type {
    UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17 : option UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__Type ;
}.
Definition UE_RadioPagingInfo_r17__root_list : list seq_elem := (
 Opt UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__Type UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__cond ::
 nil).
Definition UE_RadioPagingInfo_r17__ext_list : list typ := (
  nil).
Definition UE_RadioPagingInfo_r17__cond (z : UE_RadioPagingInfo_r17__Type) := 
(  opt_cond UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__cond (UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17 z) /\
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
Definition UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__Format : T_Format UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__Type UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__cond := seq_of_format FreqBandIndicatorNR__Format 1 maxBands UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__helper1 UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__helper2.

Opaque UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__cond UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__Format.


Definition UE_RadioPagingInfo_r17__root_Format_Type := Eval cbn in seq_format_prod UE_RadioPagingInfo_r17__root_list.
Definition UE_RadioPagingInfo_r17__root_Format_list : UE_RadioPagingInfo_r17__root_Format_Type :=
  (UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17__Format, unit_format).

Definition UE_RadioPagingInfo_r17__ext_Format_Type := Eval cbn in get_formats UE_RadioPagingInfo_r17__ext_list.
Definition UE_RadioPagingInfo_r17__ext_Format_list : UE_RadioPagingInfo_r17__ext_Format_Type :=
  unit__Format.

Definition UE_RadioPagingInfo_r17__list_type : Set := (seq_type UE_RadioPagingInfo_r17__root_list) * (seq_ext_type UE_RadioPagingInfo_r17__ext_list).
Definition UE_RadioPagingInfo_r17__list_cond (z : UE_RadioPagingInfo_r17__list_type) : Prop :=
        (seq_cond UE_RadioPagingInfo_r17__root_list (fst z)) /\ (seq_ext_cond UE_RadioPagingInfo_r17__ext_list (snd z)).
Definition UE_RadioPagingInfo_r17__list_format : T_Format UE_RadioPagingInfo_r17__list_type UE_RadioPagingInfo_r17__list_cond :=
 (* Eval compute in *) seq_ext_format UE_RadioPagingInfo_r17__root_list UE_RadioPagingInfo_r17__root_Format_list UE_RadioPagingInfo_r17__ext_list UE_RadioPagingInfo_r17__ext_Format_list.

Opaque UE_RadioPagingInfo_r17__list_format.
Definition UE_RadioPagingInfo_r17__F1 (z : UE_RadioPagingInfo_r17__Type) : UE_RadioPagingInfo_r17__list_type :=
  (((UE_RadioPagingInfo_r17__pei_SubgroupingSupportBandList_r17 z, tt)), (
tt)).
Definition UE_RadioPagingInfo_r17__F2 (y : UE_RadioPagingInfo_r17__list_type) : UE_RadioPagingInfo_r17__Type :=
  match y with
  | ((j0, _), _)=>
    make__UE_RadioPagingInfo_r17__Type j0
  end.
Definition UE_RadioPagingInfo_r17__helper1 : (forall a : UE_RadioPagingInfo_r17__Type, UE_RadioPagingInfo_r17__cond a -> UE_RadioPagingInfo_r17__list_cond (UE_RadioPagingInfo_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition UE_RadioPagingInfo_r17__helper2 : (forall a : UE_RadioPagingInfo_r17__Type, UE_RadioPagingInfo_r17__F2 (UE_RadioPagingInfo_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition UE_RadioPagingInfo_r17__helper3 : (forall b : UE_RadioPagingInfo_r17__list_type, UE_RadioPagingInfo_r17__list_cond b -> UE_RadioPagingInfo_r17__cond (UE_RadioPagingInfo_r17__F2 b) /\ UE_RadioPagingInfo_r17__F1 (UE_RadioPagingInfo_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold UE_RadioPagingInfo_r17__cond, UE_RadioPagingInfo_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition UE_RadioPagingInfo_r17__Format : T_Format UE_RadioPagingInfo_r17__Type UE_RadioPagingInfo_r17__cond :=
 proj2_format UE_RadioPagingInfo_r17__cond UE_RadioPagingInfo_r17__list_format  UE_RadioPagingInfo_r17__F1 UE_RadioPagingInfo_r17__F2 UE_RadioPagingInfo_r17__helper1 UE_RadioPagingInfo_r17__helper2 UE_RadioPagingInfo_r17__helper3.

Opaque UE_RadioPagingInfo_r17__cond UE_RadioPagingInfo_r17__Format.

