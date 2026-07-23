Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.AvailabilityCombinationId_r16.

Opaque AvailabilityCombinationId_r16__cond AvailabilityCombinationId_r16__Format.

Lemma AvailabilityCombination_r16__resourceAvailability_r16__seq_of__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma AvailabilityCombination_r16__resourceAvailability_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply AvailabilityCombination_r16__resourceAvailability_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition AvailabilityCombination_r16__resourceAvailability_r16__seq_of__Type := Z.
Definition AvailabilityCombination_r16__resourceAvailability_r16__seq_of__cond := (fun z => (0 <= z <= 7)%Z).
Definition AvailabilityCombination_r16__resourceAvailability_r16__Type := list Z.

Lemma AvailabilityCombination_r16__resourceAvailability_r16__helper1 : (0 <= 1 <= maxNrofResourceAvailabilityPerCombination_r16)%Z. unfold maxNrofResourceAvailabilityPerCombination_r16.
 lia. Qed.
Lemma AvailabilityCombination_r16__resourceAvailability_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofResourceAvailabilityPerCombination_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofResourceAvailabilityPerCombination_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply AvailabilityCombination_r16__resourceAvailability_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition AvailabilityCombination_r16__resourceAvailability_r16__cond (z : AvailabilityCombination_r16__resourceAvailability_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofResourceAvailabilityPerCombination_r16)%Z /\ (list_and AvailabilityCombination_r16__resourceAvailability_r16__seq_of__cond z) .

Record AvailabilityCombination_r16__Type : Set :=
  make__AvailabilityCombination_r16__Type {
    AvailabilityCombination_r16__availabilityCombinationId_r16 : AvailabilityCombinationId_r16__Type ;
    AvailabilityCombination_r16__resourceAvailability_r16 : AvailabilityCombination_r16__resourceAvailability_r16__Type ;
}.
Definition AvailabilityCombination_r16__list := (
 Nor AvailabilityCombinationId_r16__Type AvailabilityCombinationId_r16__cond ::
 Nor AvailabilityCombination_r16__resourceAvailability_r16__Type AvailabilityCombination_r16__resourceAvailability_r16__cond ::
 nil).
Definition AvailabilityCombination_r16__cond z := 
  AvailabilityCombinationId_r16__cond (AvailabilityCombination_r16__availabilityCombinationId_r16 z) /\
  AvailabilityCombination_r16__resourceAvailability_r16__cond (AvailabilityCombination_r16__resourceAvailability_r16 z) /\
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
Definition AvailabilityCombination_r16__resourceAvailability_r16__seq_of__Format : T_Format Z AvailabilityCombination_r16__resourceAvailability_r16__seq_of__cond :=
 ranged_int_format (0) (7) AvailabilityCombination_r16__resourceAvailability_r16__seq_of__helper1 AvailabilityCombination_r16__resourceAvailability_r16__seq_of__helper2.

Opaque AvailabilityCombination_r16__resourceAvailability_r16__seq_of__cond AvailabilityCombination_r16__resourceAvailability_r16__seq_of__Format.

Definition AvailabilityCombination_r16__resourceAvailability_r16__Format : T_Format AvailabilityCombination_r16__resourceAvailability_r16__Type AvailabilityCombination_r16__resourceAvailability_r16__cond := seq_of_format AvailabilityCombination_r16__resourceAvailability_r16__seq_of__Format 1 maxNrofResourceAvailabilityPerCombination_r16 AvailabilityCombination_r16__resourceAvailability_r16__helper1 AvailabilityCombination_r16__resourceAvailability_r16__helper2.

Opaque AvailabilityCombination_r16__resourceAvailability_r16__cond AvailabilityCombination_r16__resourceAvailability_r16__Format.


Definition AvailabilityCombination_r16__Format_Type := Eval cbn in seq_format_prod AvailabilityCombination_r16__list.
Definition AvailabilityCombination_r16__Format_list : AvailabilityCombination_r16__Format_Type :=
  (AvailabilityCombinationId_r16__Format, (AvailabilityCombination_r16__resourceAvailability_r16__Format, unit_format)).
Definition AvailabilityCombination_r16__list__Format := (*Eval compute in *) seq_format AvailabilityCombination_r16__list AvailabilityCombination_r16__Format_list.
Definition AvailabilityCombination_r16__F1 z :=
  (AvailabilityCombination_r16__availabilityCombinationId_r16 z, (AvailabilityCombination_r16__resourceAvailability_r16 z, tt)).
Definition AvailabilityCombination_r16__F2 (y : seq_type AvailabilityCombination_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__AvailabilityCombination_r16__Type i0 i1
  end.
Lemma AvailabilityCombination_r16__F1F2_cond (z : AvailabilityCombination_r16__Type)
  : AvailabilityCombination_r16__cond z ->
  (seq_cond AvailabilityCombination_r16__list (AvailabilityCombination_r16__F1 z)).
intro H. unfold AvailabilityCombination_r16__cond in H. simpl. auto. Qed.
Lemma AvailabilityCombination_r16__F1F2_cond2 (z : AvailabilityCombination_r16__Type)
 : AvailabilityCombination_r16__F2 (AvailabilityCombination_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma AvailabilityCombination_r16__F2F1_cond (y : seq_type AvailabilityCombination_r16__list)
  : seq_cond AvailabilityCombination_r16__list y ->
 (AvailabilityCombination_r16__cond (AvailabilityCombination_r16__F2 y)) /\  AvailabilityCombination_r16__F1 (AvailabilityCombination_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold AvailabilityCombination_r16__cond. simpl in *. auto.
 - simpl. unfold AvailabilityCombination_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition AvailabilityCombination_r16__Format : T_Format AvailabilityCombination_r16__Type AvailabilityCombination_r16__cond :=
        proj2_format  AvailabilityCombination_r16__cond AvailabilityCombination_r16__list__Format
    AvailabilityCombination_r16__F1 AvailabilityCombination_r16__F2 AvailabilityCombination_r16__F1F2_cond  AvailabilityCombination_r16__F1F2_cond2 AvailabilityCombination_r16__F2F1_cond.
Opaque AvailabilityCombination_r16__cond AvailabilityCombination_r16__Format.

