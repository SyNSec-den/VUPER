Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SlotFormatCombinationId.

Opaque SlotFormatCombinationId__cond SlotFormatCombinationId__Format.

Lemma SlotFormatCombination__slotFormats__seq_of__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma SlotFormatCombination__slotFormats__seq_of__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatCombination__slotFormats__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatCombination__slotFormats__seq_of__Type := Z.
Definition SlotFormatCombination__slotFormats__seq_of__cond := (fun z => (0 <= z <= 255)%Z).
Definition SlotFormatCombination__slotFormats__Type := list Z.

Lemma SlotFormatCombination__slotFormats__helper1 : (0 <= 1 <= maxNrofSlotFormatsPerCombination)%Z. unfold maxNrofSlotFormatsPerCombination.
 lia. Qed.
Lemma SlotFormatCombination__slotFormats__helper2 : to_bit_sz (Z.to_nat (maxNrofSlotFormatsPerCombination - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSlotFormatsPerCombination - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatCombination__slotFormats__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatCombination__slotFormats__cond (z : SlotFormatCombination__slotFormats__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSlotFormatsPerCombination)%Z /\ (list_and SlotFormatCombination__slotFormats__seq_of__cond z) .

Record SlotFormatCombination__Type : Set :=
  make__SlotFormatCombination__Type {
    SlotFormatCombination__slotFormatCombinationId : SlotFormatCombinationId__Type ;
    SlotFormatCombination__slotFormats : SlotFormatCombination__slotFormats__Type ;
}.
Definition SlotFormatCombination__list := (
 Nor SlotFormatCombinationId__Type SlotFormatCombinationId__cond ::
 Nor SlotFormatCombination__slotFormats__Type SlotFormatCombination__slotFormats__cond ::
 nil).
Definition SlotFormatCombination__cond z := 
  SlotFormatCombinationId__cond (SlotFormatCombination__slotFormatCombinationId z) /\
  SlotFormatCombination__slotFormats__cond (SlotFormatCombination__slotFormats z) /\
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
Definition SlotFormatCombination__slotFormats__seq_of__Format : T_Format Z SlotFormatCombination__slotFormats__seq_of__cond :=
 ranged_int_format (0) (255) SlotFormatCombination__slotFormats__seq_of__helper1 SlotFormatCombination__slotFormats__seq_of__helper2.

Opaque SlotFormatCombination__slotFormats__seq_of__cond SlotFormatCombination__slotFormats__seq_of__Format.

Definition SlotFormatCombination__slotFormats__Format : T_Format SlotFormatCombination__slotFormats__Type SlotFormatCombination__slotFormats__cond := seq_of_format SlotFormatCombination__slotFormats__seq_of__Format 1 maxNrofSlotFormatsPerCombination SlotFormatCombination__slotFormats__helper1 SlotFormatCombination__slotFormats__helper2.

Opaque SlotFormatCombination__slotFormats__cond SlotFormatCombination__slotFormats__Format.


Definition SlotFormatCombination__Format_Type := Eval cbn in seq_format_prod SlotFormatCombination__list.
Definition SlotFormatCombination__Format_list : SlotFormatCombination__Format_Type :=
  (SlotFormatCombinationId__Format, (SlotFormatCombination__slotFormats__Format, unit_format)).
Definition SlotFormatCombination__list__Format := (*Eval compute in *) seq_format SlotFormatCombination__list SlotFormatCombination__Format_list.
Definition SlotFormatCombination__F1 z :=
  (SlotFormatCombination__slotFormatCombinationId z, (SlotFormatCombination__slotFormats z, tt)).
Definition SlotFormatCombination__F2 (y : seq_type SlotFormatCombination__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SlotFormatCombination__Type i0 i1
  end.
Lemma SlotFormatCombination__F1F2_cond (z : SlotFormatCombination__Type)
  : SlotFormatCombination__cond z ->
  (seq_cond SlotFormatCombination__list (SlotFormatCombination__F1 z)).
intro H. unfold SlotFormatCombination__cond in H. simpl. auto. Qed.
Lemma SlotFormatCombination__F1F2_cond2 (z : SlotFormatCombination__Type)
 : SlotFormatCombination__F2 (SlotFormatCombination__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SlotFormatCombination__F2F1_cond (y : seq_type SlotFormatCombination__list)
  : seq_cond SlotFormatCombination__list y ->
 (SlotFormatCombination__cond (SlotFormatCombination__F2 y)) /\  SlotFormatCombination__F1 (SlotFormatCombination__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SlotFormatCombination__cond. simpl in *. auto.
 - simpl. unfold SlotFormatCombination__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SlotFormatCombination__Format : T_Format SlotFormatCombination__Type SlotFormatCombination__cond :=
        proj2_format  SlotFormatCombination__cond SlotFormatCombination__list__Format
    SlotFormatCombination__F1 SlotFormatCombination__F2 SlotFormatCombination__F1F2_cond  SlotFormatCombination__F1F2_cond2 SlotFormatCombination__F2F1_cond.
Opaque SlotFormatCombination__cond SlotFormatCombination__Format.

