Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Definition UERadioPagingInformation_IEs__supportedBandListNRForPaging__Type := list FreqBandIndicatorNR__Type.

Lemma UERadioPagingInformation_IEs__supportedBandListNRForPaging__helper1 : (0 <= 1 <= maxBands)%Z. unfold maxBands.
 lia. Qed.
Lemma UERadioPagingInformation_IEs__supportedBandListNRForPaging__helper2 : to_bit_sz (Z.to_nat (maxBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UERadioPagingInformation_IEs__supportedBandListNRForPaging__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UERadioPagingInformation_IEs__supportedBandListNRForPaging__cond (z : UERadioPagingInformation_IEs__supportedBandListNRForPaging__Type) :=  (1 <= Z.of_nat (length z) <= maxBands)%Z /\ (list_and FreqBandIndicatorNR__cond z) .

Require Import NR.UERadioPagingInformation_v15e0_IEs.

Opaque UERadioPagingInformation_v15e0_IEs__cond UERadioPagingInformation_v15e0_IEs__Format.

Record UERadioPagingInformation_IEs__Type : Set :=
  make__UERadioPagingInformation_IEs__Type {
    UERadioPagingInformation_IEs__supportedBandListNRForPaging : option UERadioPagingInformation_IEs__supportedBandListNRForPaging__Type ;
    UERadioPagingInformation_IEs__nonCriticalExtension : option UERadioPagingInformation_v15e0_IEs__Type ;
}.
Definition UERadioPagingInformation_IEs__list := (
 Opt UERadioPagingInformation_IEs__supportedBandListNRForPaging__Type UERadioPagingInformation_IEs__supportedBandListNRForPaging__cond ::
 Opt UERadioPagingInformation_v15e0_IEs__Type UERadioPagingInformation_v15e0_IEs__cond ::
 nil).
Definition UERadioPagingInformation_IEs__cond z := 
  opt_cond UERadioPagingInformation_IEs__supportedBandListNRForPaging__cond (UERadioPagingInformation_IEs__supportedBandListNRForPaging z) /\
  opt_cond UERadioPagingInformation_v15e0_IEs__cond (UERadioPagingInformation_IEs__nonCriticalExtension z) /\
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
Definition UERadioPagingInformation_IEs__supportedBandListNRForPaging__Format : T_Format UERadioPagingInformation_IEs__supportedBandListNRForPaging__Type UERadioPagingInformation_IEs__supportedBandListNRForPaging__cond := seq_of_format FreqBandIndicatorNR__Format 1 maxBands UERadioPagingInformation_IEs__supportedBandListNRForPaging__helper1 UERadioPagingInformation_IEs__supportedBandListNRForPaging__helper2.

Opaque UERadioPagingInformation_IEs__supportedBandListNRForPaging__cond UERadioPagingInformation_IEs__supportedBandListNRForPaging__Format.


Definition UERadioPagingInformation_IEs__Format_Type := Eval cbn in seq_format_prod UERadioPagingInformation_IEs__list.
Definition UERadioPagingInformation_IEs__Format_list : UERadioPagingInformation_IEs__Format_Type :=
  (UERadioPagingInformation_IEs__supportedBandListNRForPaging__Format, (UERadioPagingInformation_v15e0_IEs__Format, unit_format)).
Definition UERadioPagingInformation_IEs__list__Format := (*Eval compute in *) seq_format UERadioPagingInformation_IEs__list UERadioPagingInformation_IEs__Format_list.
Definition UERadioPagingInformation_IEs__F1 z :=
  (UERadioPagingInformation_IEs__supportedBandListNRForPaging z, (UERadioPagingInformation_IEs__nonCriticalExtension z, tt)).
Definition UERadioPagingInformation_IEs__F2 (y : seq_type UERadioPagingInformation_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UERadioPagingInformation_IEs__Type i0 i1
  end.
Lemma UERadioPagingInformation_IEs__F1F2_cond (z : UERadioPagingInformation_IEs__Type)
  : UERadioPagingInformation_IEs__cond z ->
  (seq_cond UERadioPagingInformation_IEs__list (UERadioPagingInformation_IEs__F1 z)).
intro H. unfold UERadioPagingInformation_IEs__cond in H. simpl. auto. Qed.
Lemma UERadioPagingInformation_IEs__F1F2_cond2 (z : UERadioPagingInformation_IEs__Type)
 : UERadioPagingInformation_IEs__F2 (UERadioPagingInformation_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UERadioPagingInformation_IEs__F2F1_cond (y : seq_type UERadioPagingInformation_IEs__list)
  : seq_cond UERadioPagingInformation_IEs__list y ->
 (UERadioPagingInformation_IEs__cond (UERadioPagingInformation_IEs__F2 y)) /\  UERadioPagingInformation_IEs__F1 (UERadioPagingInformation_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UERadioPagingInformation_IEs__cond. simpl in *. auto.
 - simpl. unfold UERadioPagingInformation_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UERadioPagingInformation_IEs__Format : T_Format UERadioPagingInformation_IEs__Type UERadioPagingInformation_IEs__cond :=
        proj2_format  UERadioPagingInformation_IEs__cond UERadioPagingInformation_IEs__list__Format
    UERadioPagingInformation_IEs__F1 UERadioPagingInformation_IEs__F2 UERadioPagingInformation_IEs__F1F2_cond  UERadioPagingInformation_IEs__F1F2_cond2 UERadioPagingInformation_IEs__F2F1_cond.
Opaque UERadioPagingInformation_IEs__cond UERadioPagingInformation_IEs__Format.

