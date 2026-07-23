Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NeedForNCSG_EUTRA_r17.

Opaque NeedForNCSG_EUTRA_r17__cond NeedForNCSG_EUTRA_r17__Format.

Definition NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type := list NeedForNCSG_EUTRA_r17__Type.

Lemma NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__helper1 : (0 <= 1 <= maxBandsEUTRA)%Z. unfold maxBandsEUTRA.
 lia. Qed.
Lemma NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__helper2 : to_bit_sz (Z.to_nat (maxBandsEUTRA - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBandsEUTRA - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__cond (z : NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxBandsEUTRA)%Z /\ (list_and NeedForNCSG_EUTRA_r17__cond z) .

Record NeedForGapNCSG_InfoEUTRA_r17__Type : Set :=
  make__NeedForGapNCSG_InfoEUTRA_r17__Type {
    NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17 : NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type ;
}.
Definition NeedForGapNCSG_InfoEUTRA_r17__list := (
 Nor NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__cond ::
 nil).
Definition NeedForGapNCSG_InfoEUTRA_r17__cond z := 
  NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__cond (NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17 z) /\
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
Definition NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Format : T_Format NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Type NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__cond := seq_of_format NeedForNCSG_EUTRA_r17__Format 1 maxBandsEUTRA NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__helper1 NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__helper2.

Opaque NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__cond NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Format.


Definition NeedForGapNCSG_InfoEUTRA_r17__Format_Type := Eval cbn in seq_format_prod NeedForGapNCSG_InfoEUTRA_r17__list.
Definition NeedForGapNCSG_InfoEUTRA_r17__Format_list : NeedForGapNCSG_InfoEUTRA_r17__Format_Type :=
  (NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17__Format, unit_format).
Definition NeedForGapNCSG_InfoEUTRA_r17__list__Format := (*Eval compute in *) seq_format NeedForGapNCSG_InfoEUTRA_r17__list NeedForGapNCSG_InfoEUTRA_r17__Format_list.
Definition NeedForGapNCSG_InfoEUTRA_r17__F1 z :=
  (NeedForGapNCSG_InfoEUTRA_r17__needForNCSG_EUTRA_r17 z, tt).
Definition NeedForGapNCSG_InfoEUTRA_r17__F2 (y : seq_type NeedForGapNCSG_InfoEUTRA_r17__list) :=
  match y with
  | (i0, _)=>
    make__NeedForGapNCSG_InfoEUTRA_r17__Type i0
  end.
Lemma NeedForGapNCSG_InfoEUTRA_r17__F1F2_cond (z : NeedForGapNCSG_InfoEUTRA_r17__Type)
  : NeedForGapNCSG_InfoEUTRA_r17__cond z ->
  (seq_cond NeedForGapNCSG_InfoEUTRA_r17__list (NeedForGapNCSG_InfoEUTRA_r17__F1 z)).
intro H. unfold NeedForGapNCSG_InfoEUTRA_r17__cond in H. simpl. auto. Qed.
Lemma NeedForGapNCSG_InfoEUTRA_r17__F1F2_cond2 (z : NeedForGapNCSG_InfoEUTRA_r17__Type)
 : NeedForGapNCSG_InfoEUTRA_r17__F2 (NeedForGapNCSG_InfoEUTRA_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NeedForGapNCSG_InfoEUTRA_r17__F2F1_cond (y : seq_type NeedForGapNCSG_InfoEUTRA_r17__list)
  : seq_cond NeedForGapNCSG_InfoEUTRA_r17__list y ->
 (NeedForGapNCSG_InfoEUTRA_r17__cond (NeedForGapNCSG_InfoEUTRA_r17__F2 y)) /\  NeedForGapNCSG_InfoEUTRA_r17__F1 (NeedForGapNCSG_InfoEUTRA_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NeedForGapNCSG_InfoEUTRA_r17__cond. simpl in *. auto.
 - simpl. unfold NeedForGapNCSG_InfoEUTRA_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NeedForGapNCSG_InfoEUTRA_r17__Format : T_Format NeedForGapNCSG_InfoEUTRA_r17__Type NeedForGapNCSG_InfoEUTRA_r17__cond :=
        proj2_format  NeedForGapNCSG_InfoEUTRA_r17__cond NeedForGapNCSG_InfoEUTRA_r17__list__Format
    NeedForGapNCSG_InfoEUTRA_r17__F1 NeedForGapNCSG_InfoEUTRA_r17__F2 NeedForGapNCSG_InfoEUTRA_r17__F1F2_cond  NeedForGapNCSG_InfoEUTRA_r17__F1F2_cond2 NeedForGapNCSG_InfoEUTRA_r17__F2F1_cond.
Opaque NeedForGapNCSG_InfoEUTRA_r17__cond NeedForGapNCSG_InfoEUTRA_r17__Format.

