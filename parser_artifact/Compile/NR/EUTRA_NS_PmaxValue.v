Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma EUTRA_NS_PmaxValue__additionalPmax__helper1 : (-30 <= 33)%Z.  lia. Qed.
Lemma EUTRA_NS_PmaxValue__additionalPmax__helper2 : to_bit_sz (Z.to_nat (33 - -30)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (33 - -30))%Z). { apply Zorder.Zle_minus_le_0. apply EUTRA_NS_PmaxValue__additionalPmax__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EUTRA_NS_PmaxValue__additionalPmax__Type := Z.
Definition EUTRA_NS_PmaxValue__additionalPmax__cond := (fun z => (-30 <= z <= 33)%Z).
Lemma EUTRA_NS_PmaxValue__additionalSpectrumEmission__helper1 : (1 <= 288)%Z.  lia. Qed.
Lemma EUTRA_NS_PmaxValue__additionalSpectrumEmission__helper2 : to_bit_sz (Z.to_nat (288 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (288 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EUTRA_NS_PmaxValue__additionalSpectrumEmission__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EUTRA_NS_PmaxValue__additionalSpectrumEmission__Type := Z.
Definition EUTRA_NS_PmaxValue__additionalSpectrumEmission__cond := (fun z => (1 <= z <= 288)%Z).
Record EUTRA_NS_PmaxValue__Type : Set :=
  make__EUTRA_NS_PmaxValue__Type {
    EUTRA_NS_PmaxValue__additionalPmax : option Z ;
    EUTRA_NS_PmaxValue__additionalSpectrumEmission : option Z ;
}.
Definition EUTRA_NS_PmaxValue__list := (
 Opt Z EUTRA_NS_PmaxValue__additionalPmax__cond ::
 Opt Z EUTRA_NS_PmaxValue__additionalSpectrumEmission__cond ::
 nil).
Definition EUTRA_NS_PmaxValue__cond z := 
  opt_cond EUTRA_NS_PmaxValue__additionalPmax__cond (EUTRA_NS_PmaxValue__additionalPmax z) /\
  opt_cond EUTRA_NS_PmaxValue__additionalSpectrumEmission__cond (EUTRA_NS_PmaxValue__additionalSpectrumEmission z) /\
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
Definition EUTRA_NS_PmaxValue__additionalPmax__Format : T_Format Z EUTRA_NS_PmaxValue__additionalPmax__cond :=
 ranged_int_format (-30) (33) EUTRA_NS_PmaxValue__additionalPmax__helper1 EUTRA_NS_PmaxValue__additionalPmax__helper2.

Opaque EUTRA_NS_PmaxValue__additionalPmax__cond EUTRA_NS_PmaxValue__additionalPmax__Format.

Definition EUTRA_NS_PmaxValue__additionalSpectrumEmission__Format : T_Format Z EUTRA_NS_PmaxValue__additionalSpectrumEmission__cond :=
 ranged_int_format (1) (288) EUTRA_NS_PmaxValue__additionalSpectrumEmission__helper1 EUTRA_NS_PmaxValue__additionalSpectrumEmission__helper2.

Opaque EUTRA_NS_PmaxValue__additionalSpectrumEmission__cond EUTRA_NS_PmaxValue__additionalSpectrumEmission__Format.


Definition EUTRA_NS_PmaxValue__Format_Type := Eval cbn in seq_format_prod EUTRA_NS_PmaxValue__list.
Definition EUTRA_NS_PmaxValue__Format_list : EUTRA_NS_PmaxValue__Format_Type :=
  (EUTRA_NS_PmaxValue__additionalPmax__Format, (EUTRA_NS_PmaxValue__additionalSpectrumEmission__Format, unit_format)).
Definition EUTRA_NS_PmaxValue__list__Format := (*Eval compute in *) seq_format EUTRA_NS_PmaxValue__list EUTRA_NS_PmaxValue__Format_list.
Definition EUTRA_NS_PmaxValue__F1 z :=
  (EUTRA_NS_PmaxValue__additionalPmax z, (EUTRA_NS_PmaxValue__additionalSpectrumEmission z, tt)).
Definition EUTRA_NS_PmaxValue__F2 (y : seq_type EUTRA_NS_PmaxValue__list) :=
  match y with
  | (i0, (i1, _))=>
    make__EUTRA_NS_PmaxValue__Type i0 i1
  end.
Lemma EUTRA_NS_PmaxValue__F1F2_cond (z : EUTRA_NS_PmaxValue__Type)
  : EUTRA_NS_PmaxValue__cond z ->
  (seq_cond EUTRA_NS_PmaxValue__list (EUTRA_NS_PmaxValue__F1 z)).
intro H. unfold EUTRA_NS_PmaxValue__cond in H. simpl. auto. Qed.
Lemma EUTRA_NS_PmaxValue__F1F2_cond2 (z : EUTRA_NS_PmaxValue__Type)
 : EUTRA_NS_PmaxValue__F2 (EUTRA_NS_PmaxValue__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EUTRA_NS_PmaxValue__F2F1_cond (y : seq_type EUTRA_NS_PmaxValue__list)
  : seq_cond EUTRA_NS_PmaxValue__list y ->
 (EUTRA_NS_PmaxValue__cond (EUTRA_NS_PmaxValue__F2 y)) /\  EUTRA_NS_PmaxValue__F1 (EUTRA_NS_PmaxValue__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EUTRA_NS_PmaxValue__cond. simpl in *. auto.
 - simpl. unfold EUTRA_NS_PmaxValue__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EUTRA_NS_PmaxValue__Format : T_Format EUTRA_NS_PmaxValue__Type EUTRA_NS_PmaxValue__cond :=
        proj2_format  EUTRA_NS_PmaxValue__cond EUTRA_NS_PmaxValue__list__Format
    EUTRA_NS_PmaxValue__F1 EUTRA_NS_PmaxValue__F2 EUTRA_NS_PmaxValue__F1F2_cond  EUTRA_NS_PmaxValue__F1F2_cond2 EUTRA_NS_PmaxValue__F2F1_cond.
Opaque EUTRA_NS_PmaxValue__cond EUTRA_NS_PmaxValue__Format.

