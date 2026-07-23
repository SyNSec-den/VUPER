Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__helper1 : (1 <= 7)%Z.  lia. Qed.
Lemma NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__helper2 : to_bit_sz (Z.to_nat (7 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__Type := Z.
Definition NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__cond := (fun z => (1 <= z <= 7)%Z).
Lemma NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__helper1 : (1 <= 7)%Z.  lia. Qed.
Lemma NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__helper2 : to_bit_sz (Z.to_nat (7 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__Type := Z.
Definition NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__cond := (fun z => (1 <= z <= 7)%Z).
Record NZP_CSI_RS_Pairing_r17__Type : Set :=
  make__NZP_CSI_RS_Pairing_r17__Type {
    NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17 : Z ;
    NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17 : Z ;
}.
Definition NZP_CSI_RS_Pairing_r17__list := (
 Nor Z NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__cond ::
 Nor Z NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__cond ::
 nil).
Definition NZP_CSI_RS_Pairing_r17__cond z := 
  NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__cond (NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17 z) /\
  NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__cond (NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17 z) /\
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
Definition NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__Format : T_Format Z NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__cond :=
 ranged_int_format (1) (7) NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__helper1 NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__helper2.

Opaque NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__cond NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__Format.

Definition NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__Format : T_Format Z NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__cond :=
 ranged_int_format (1) (7) NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__helper1 NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__helper2.

Opaque NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__cond NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__Format.


Definition NZP_CSI_RS_Pairing_r17__Format_Type := Eval cbn in seq_format_prod NZP_CSI_RS_Pairing_r17__list.
Definition NZP_CSI_RS_Pairing_r17__Format_list : NZP_CSI_RS_Pairing_r17__Format_Type :=
  (NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17__Format, (NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17__Format, unit_format)).
Definition NZP_CSI_RS_Pairing_r17__list__Format := (*Eval compute in *) seq_format NZP_CSI_RS_Pairing_r17__list NZP_CSI_RS_Pairing_r17__Format_list.
Definition NZP_CSI_RS_Pairing_r17__F1 z :=
  (NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId1_r17 z, (NZP_CSI_RS_Pairing_r17__nzp_CSI_RS_ResourceId2_r17 z, tt)).
Definition NZP_CSI_RS_Pairing_r17__F2 (y : seq_type NZP_CSI_RS_Pairing_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__NZP_CSI_RS_Pairing_r17__Type i0 i1
  end.
Lemma NZP_CSI_RS_Pairing_r17__F1F2_cond (z : NZP_CSI_RS_Pairing_r17__Type)
  : NZP_CSI_RS_Pairing_r17__cond z ->
  (seq_cond NZP_CSI_RS_Pairing_r17__list (NZP_CSI_RS_Pairing_r17__F1 z)).
intro H. unfold NZP_CSI_RS_Pairing_r17__cond in H. simpl. auto. Qed.
Lemma NZP_CSI_RS_Pairing_r17__F1F2_cond2 (z : NZP_CSI_RS_Pairing_r17__Type)
 : NZP_CSI_RS_Pairing_r17__F2 (NZP_CSI_RS_Pairing_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NZP_CSI_RS_Pairing_r17__F2F1_cond (y : seq_type NZP_CSI_RS_Pairing_r17__list)
  : seq_cond NZP_CSI_RS_Pairing_r17__list y ->
 (NZP_CSI_RS_Pairing_r17__cond (NZP_CSI_RS_Pairing_r17__F2 y)) /\  NZP_CSI_RS_Pairing_r17__F1 (NZP_CSI_RS_Pairing_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NZP_CSI_RS_Pairing_r17__cond. simpl in *. auto.
 - simpl. unfold NZP_CSI_RS_Pairing_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NZP_CSI_RS_Pairing_r17__Format : T_Format NZP_CSI_RS_Pairing_r17__Type NZP_CSI_RS_Pairing_r17__cond :=
        proj2_format  NZP_CSI_RS_Pairing_r17__cond NZP_CSI_RS_Pairing_r17__list__Format
    NZP_CSI_RS_Pairing_r17__F1 NZP_CSI_RS_Pairing_r17__F2 NZP_CSI_RS_Pairing_r17__F1F2_cond  NZP_CSI_RS_Pairing_r17__F1F2_cond2 NZP_CSI_RS_Pairing_r17__F2F1_cond.
Opaque NZP_CSI_RS_Pairing_r17__cond NZP_CSI_RS_Pairing_r17__Format.

