Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandParameters_v1540.

Opaque BandParameters_v1540__cond BandParameters_v1540__Format.

Definition BandCombination_v1540__bandList_v1540__Type := list BandParameters_v1540__Type.

Lemma BandCombination_v1540__bandList_v1540__helper1 : (0 <= 1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma BandCombination_v1540__bandList_v1540__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombination_v1540__bandList_v1540__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombination_v1540__bandList_v1540__cond (z : BandCombination_v1540__bandList_v1540__Type) :=  (1 <= Z.of_nat (length z) <= maxSimultaneousBands)%Z /\ (list_and BandParameters_v1540__cond z) .

Require Import NR.CA_ParametersNR_v1540.

Opaque CA_ParametersNR_v1540__cond CA_ParametersNR_v1540__Format.

Record BandCombination_v1540__Type : Set :=
  make__BandCombination_v1540__Type {
    BandCombination_v1540__bandList_v1540 : BandCombination_v1540__bandList_v1540__Type ;
    BandCombination_v1540__ca_ParametersNR_v1540 : option CA_ParametersNR_v1540__Type ;
}.
Definition BandCombination_v1540__list := (
 Nor BandCombination_v1540__bandList_v1540__Type BandCombination_v1540__bandList_v1540__cond ::
 Opt CA_ParametersNR_v1540__Type CA_ParametersNR_v1540__cond ::
 nil).
Definition BandCombination_v1540__cond z := 
  BandCombination_v1540__bandList_v1540__cond (BandCombination_v1540__bandList_v1540 z) /\
  opt_cond CA_ParametersNR_v1540__cond (BandCombination_v1540__ca_ParametersNR_v1540 z) /\
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
Definition BandCombination_v1540__bandList_v1540__Format : T_Format BandCombination_v1540__bandList_v1540__Type BandCombination_v1540__bandList_v1540__cond := seq_of_format BandParameters_v1540__Format 1 maxSimultaneousBands BandCombination_v1540__bandList_v1540__helper1 BandCombination_v1540__bandList_v1540__helper2.

Opaque BandCombination_v1540__bandList_v1540__cond BandCombination_v1540__bandList_v1540__Format.


Definition BandCombination_v1540__Format_Type := Eval cbn in seq_format_prod BandCombination_v1540__list.
Definition BandCombination_v1540__Format_list : BandCombination_v1540__Format_Type :=
  (BandCombination_v1540__bandList_v1540__Format, (CA_ParametersNR_v1540__Format, unit_format)).
Definition BandCombination_v1540__list__Format := (*Eval compute in *) seq_format BandCombination_v1540__list BandCombination_v1540__Format_list.
Definition BandCombination_v1540__F1 z :=
  (BandCombination_v1540__bandList_v1540 z, (BandCombination_v1540__ca_ParametersNR_v1540 z, tt)).
Definition BandCombination_v1540__F2 (y : seq_type BandCombination_v1540__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandCombination_v1540__Type i0 i1
  end.
Lemma BandCombination_v1540__F1F2_cond (z : BandCombination_v1540__Type)
  : BandCombination_v1540__cond z ->
  (seq_cond BandCombination_v1540__list (BandCombination_v1540__F1 z)).
intro H. unfold BandCombination_v1540__cond in H. simpl. auto. Qed.
Lemma BandCombination_v1540__F1F2_cond2 (z : BandCombination_v1540__Type)
 : BandCombination_v1540__F2 (BandCombination_v1540__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombination_v1540__F2F1_cond (y : seq_type BandCombination_v1540__list)
  : seq_cond BandCombination_v1540__list y ->
 (BandCombination_v1540__cond (BandCombination_v1540__F2 y)) /\  BandCombination_v1540__F1 (BandCombination_v1540__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombination_v1540__cond. simpl in *. auto.
 - simpl. unfold BandCombination_v1540__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombination_v1540__Format : T_Format BandCombination_v1540__Type BandCombination_v1540__cond :=
        proj2_format  BandCombination_v1540__cond BandCombination_v1540__list__Format
    BandCombination_v1540__F1 BandCombination_v1540__F2 BandCombination_v1540__F1F2_cond  BandCombination_v1540__F1F2_cond2 BandCombination_v1540__F2F1_cond.
Opaque BandCombination_v1540__cond BandCombination_v1540__Format.

