Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__helper1 : (1 <= 7)%Z.  lia. Qed.
Lemma CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__helper2 : to_bit_sz (Z.to_nat (7 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__Type := Z.
Definition CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__cond := (fun z => (1 <= z <= 7)%Z).
Require Import NR.NZP_CSI_RS_Pairing_r17.

Opaque NZP_CSI_RS_Pairing_r17__cond NZP_CSI_RS_Pairing_r17__Format.

Require Import NR.NZP_CSI_RS_Pairing_r17.

Opaque NZP_CSI_RS_Pairing_r17__cond NZP_CSI_RS_Pairing_r17__Format.

Record CMRGroupingAndPairing_r17__Type : Set :=
  make__CMRGroupingAndPairing_r17__Type {
    CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17 : Z ;
    CMRGroupingAndPairing_r17__pair1OfNZP_CSI_RS_r17 : option NZP_CSI_RS_Pairing_r17__Type ;
    CMRGroupingAndPairing_r17__pair2OfNZP_CSI_RS_r17 : option NZP_CSI_RS_Pairing_r17__Type ;
}.
Definition CMRGroupingAndPairing_r17__list := (
 Nor Z CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__cond ::
 Opt NZP_CSI_RS_Pairing_r17__Type NZP_CSI_RS_Pairing_r17__cond ::
 Opt NZP_CSI_RS_Pairing_r17__Type NZP_CSI_RS_Pairing_r17__cond ::
 nil).
Definition CMRGroupingAndPairing_r17__cond z := 
  CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__cond (CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17 z) /\
  opt_cond NZP_CSI_RS_Pairing_r17__cond (CMRGroupingAndPairing_r17__pair1OfNZP_CSI_RS_r17 z) /\
  opt_cond NZP_CSI_RS_Pairing_r17__cond (CMRGroupingAndPairing_r17__pair2OfNZP_CSI_RS_r17 z) /\
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
Definition CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__Format : T_Format Z CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__cond :=
 ranged_int_format (1) (7) CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__helper1 CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__helper2.

Opaque CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__cond CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__Format.


Definition CMRGroupingAndPairing_r17__Format_Type := Eval cbn in seq_format_prod CMRGroupingAndPairing_r17__list.
Definition CMRGroupingAndPairing_r17__Format_list : CMRGroupingAndPairing_r17__Format_Type :=
  (CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17__Format, (NZP_CSI_RS_Pairing_r17__Format, (NZP_CSI_RS_Pairing_r17__Format, unit_format))).
Definition CMRGroupingAndPairing_r17__list__Format := (*Eval compute in *) seq_format CMRGroupingAndPairing_r17__list CMRGroupingAndPairing_r17__Format_list.
Definition CMRGroupingAndPairing_r17__F1 z :=
  (CMRGroupingAndPairing_r17__nrofResourcesGroup1_r17 z, (CMRGroupingAndPairing_r17__pair1OfNZP_CSI_RS_r17 z, (CMRGroupingAndPairing_r17__pair2OfNZP_CSI_RS_r17 z, tt))).
Definition CMRGroupingAndPairing_r17__F2 (y : seq_type CMRGroupingAndPairing_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CMRGroupingAndPairing_r17__Type i0 i1 i2
  end.
Lemma CMRGroupingAndPairing_r17__F1F2_cond (z : CMRGroupingAndPairing_r17__Type)
  : CMRGroupingAndPairing_r17__cond z ->
  (seq_cond CMRGroupingAndPairing_r17__list (CMRGroupingAndPairing_r17__F1 z)).
intro H. unfold CMRGroupingAndPairing_r17__cond in H. simpl. auto. Qed.
Lemma CMRGroupingAndPairing_r17__F1F2_cond2 (z : CMRGroupingAndPairing_r17__Type)
 : CMRGroupingAndPairing_r17__F2 (CMRGroupingAndPairing_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CMRGroupingAndPairing_r17__F2F1_cond (y : seq_type CMRGroupingAndPairing_r17__list)
  : seq_cond CMRGroupingAndPairing_r17__list y ->
 (CMRGroupingAndPairing_r17__cond (CMRGroupingAndPairing_r17__F2 y)) /\  CMRGroupingAndPairing_r17__F1 (CMRGroupingAndPairing_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CMRGroupingAndPairing_r17__cond. simpl in *. auto.
 - simpl. unfold CMRGroupingAndPairing_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CMRGroupingAndPairing_r17__Format : T_Format CMRGroupingAndPairing_r17__Type CMRGroupingAndPairing_r17__cond :=
        proj2_format  CMRGroupingAndPairing_r17__cond CMRGroupingAndPairing_r17__list__Format
    CMRGroupingAndPairing_r17__F1 CMRGroupingAndPairing_r17__F2 CMRGroupingAndPairing_r17__F1F2_cond  CMRGroupingAndPairing_r17__F1F2_cond2 CMRGroupingAndPairing_r17__F2F1_cond.
Opaque CMRGroupingAndPairing_r17__cond CMRGroupingAndPairing_r17__Format.

