Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SlotFormatCombination.

Opaque SlotFormatCombination__cond SlotFormatCombination__Format.

Definition SlotFormatCombinationsPerCell__slotFormatCombinations__Type := list SlotFormatCombination__Type.

Lemma SlotFormatCombinationsPerCell__slotFormatCombinations__helper1 : (0 <= 1 <= maxNrofSlotFormatCombinationsPerSet)%Z. unfold maxNrofSlotFormatCombinationsPerSet.
 lia. Qed.
Lemma SlotFormatCombinationsPerCell__slotFormatCombinations__helper2 : to_bit_sz (Z.to_nat (maxNrofSlotFormatCombinationsPerSet - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSlotFormatCombinationsPerSet - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatCombinationsPerCell__slotFormatCombinations__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatCombinationsPerCell__slotFormatCombinations__cond (z : SlotFormatCombinationsPerCell__slotFormatCombinations__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSlotFormatCombinationsPerSet)%Z /\ (list_and SlotFormatCombination__cond z) .

Lemma SlotFormatCombinationsPerCell__positionInDCI__helper1 : (0 <= maxSFI_DCI_PayloadSize_1)%Z. unfold maxSFI_DCI_PayloadSize_1.
 lia. Qed.
Lemma SlotFormatCombinationsPerCell__positionInDCI__helper2 : to_bit_sz (Z.to_nat (maxSFI_DCI_PayloadSize_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSFI_DCI_PayloadSize_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatCombinationsPerCell__positionInDCI__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatCombinationsPerCell__positionInDCI__Type := Z.
Definition SlotFormatCombinationsPerCell__positionInDCI__cond := (fun z => (0 <= z <= maxSFI_DCI_PayloadSize_1)%Z).
Inductive SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Type : Set :=
 | SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__enabled
.
Definition SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__cond := (fun (_ : SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Type) => True).
Lemma SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__nat__helper.

Definition SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F1 t :=
  match t with
  | SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__enabled => 0
  end.
Definition SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F2 n :=
  match n with
  | 0 => SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__enabled
  | _ => SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__enabled
  end.
Lemma SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F1F2 : forall x : SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Type, (SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F1 x <= 0) /\ SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F2 (SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F1 x) = x. imp_solve. Qed.
Lemma SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F2F1 : forall (y : nat) (H : y <= 0), SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F1 (SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F2 y) = y. enum_solve H y. Qed.

Record SlotFormatCombinationsPerCell__ext0O__Type : Set :=
  make__SlotFormatCombinationsPerCell__ext0O__Type {
    SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16 : option SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Type ;
}.
Definition SlotFormatCombinationsPerCell__ext0O__list := (
 Opt SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Type SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__cond ::
 nil).
Definition SlotFormatCombinationsPerCell__ext0O__cond z := 
  opt_cond SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__cond (SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16 z) /\
  True.

Definition SlotFormatCombinationsPerCell__ext0__Type := SlotFormatCombinationsPerCell__ext0O__Type.
Definition SlotFormatCombinationsPerCell__ext0__cond := SlotFormatCombinationsPerCell__ext0O__cond.

Record SlotFormatCombinationsPerCell__Type : Set :=
  make__SlotFormatCombinationsPerCell__Type {
    SlotFormatCombinationsPerCell__servingCellId : ServCellIndex__Type ;
    SlotFormatCombinationsPerCell__subcarrierSpacing : SubcarrierSpacing__Type ;
    SlotFormatCombinationsPerCell__subcarrierSpacing2 : option SubcarrierSpacing__Type ;
    SlotFormatCombinationsPerCell__slotFormatCombinations : option SlotFormatCombinationsPerCell__slotFormatCombinations__Type ;
    SlotFormatCombinationsPerCell__positionInDCI : option Z ;
    SlotFormatCombinationsPerCell__ext0 : option SlotFormatCombinationsPerCell__ext0__Type ;
}.
Definition SlotFormatCombinationsPerCell__root_list : list seq_elem := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt SlotFormatCombinationsPerCell__slotFormatCombinations__Type SlotFormatCombinationsPerCell__slotFormatCombinations__cond ::
 Opt Z SlotFormatCombinationsPerCell__positionInDCI__cond ::
 nil).
Definition SlotFormatCombinationsPerCell__ext_list : list typ := (
  typ_cons SlotFormatCombinationsPerCell__ext0__Type SlotFormatCombinationsPerCell__ext0__cond ::
  nil).
Definition SlotFormatCombinationsPerCell__cond (z : SlotFormatCombinationsPerCell__Type) := 
(  ServCellIndex__cond (SlotFormatCombinationsPerCell__servingCellId z) /\
  SubcarrierSpacing__cond (SlotFormatCombinationsPerCell__subcarrierSpacing z) /\
  opt_cond SubcarrierSpacing__cond (SlotFormatCombinationsPerCell__subcarrierSpacing2 z) /\
  opt_cond SlotFormatCombinationsPerCell__slotFormatCombinations__cond (SlotFormatCombinationsPerCell__slotFormatCombinations z) /\
  opt_cond SlotFormatCombinationsPerCell__positionInDCI__cond (SlotFormatCombinationsPerCell__positionInDCI z) /\
  True) /\ 
(  opt_cond SlotFormatCombinationsPerCell__ext0__cond (SlotFormatCombinationsPerCell__ext0 z) /\
  True).


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
Definition SlotFormatCombinationsPerCell__slotFormatCombinations__Format : T_Format SlotFormatCombinationsPerCell__slotFormatCombinations__Type SlotFormatCombinationsPerCell__slotFormatCombinations__cond := seq_of_format SlotFormatCombination__Format 1 maxNrofSlotFormatCombinationsPerSet SlotFormatCombinationsPerCell__slotFormatCombinations__helper1 SlotFormatCombinationsPerCell__slotFormatCombinations__helper2.

Opaque SlotFormatCombinationsPerCell__slotFormatCombinations__cond SlotFormatCombinationsPerCell__slotFormatCombinations__Format.

Definition SlotFormatCombinationsPerCell__positionInDCI__Format : T_Format Z SlotFormatCombinationsPerCell__positionInDCI__cond :=
 ranged_int_format (0) (maxSFI_DCI_PayloadSize_1) SlotFormatCombinationsPerCell__positionInDCI__helper1 SlotFormatCombinationsPerCell__positionInDCI__helper2.

Opaque SlotFormatCombinationsPerCell__positionInDCI__cond SlotFormatCombinationsPerCell__positionInDCI__Format.

Definition SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Format : T_Format SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__nat__Format SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F1 SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F2 SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F1F2 SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__F2F1.

Opaque SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__cond SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Format.


Definition SlotFormatCombinationsPerCell__ext0O__Format_Type := Eval cbn in seq_format_prod SlotFormatCombinationsPerCell__ext0O__list.
Definition SlotFormatCombinationsPerCell__ext0O__Format_list : SlotFormatCombinationsPerCell__ext0O__Format_Type :=
  (SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16__Format, unit_format).
Definition SlotFormatCombinationsPerCell__ext0O__list__Format := (*Eval compute in *) seq_format SlotFormatCombinationsPerCell__ext0O__list SlotFormatCombinationsPerCell__ext0O__Format_list.
Definition SlotFormatCombinationsPerCell__ext0O__F1 z :=
  (SlotFormatCombinationsPerCell__ext0O__enableConfiguredUL_r16 z, tt).
Definition SlotFormatCombinationsPerCell__ext0O__F2 (y : seq_type SlotFormatCombinationsPerCell__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SlotFormatCombinationsPerCell__ext0O__Type i0
  end.
Lemma SlotFormatCombinationsPerCell__ext0O__F1F2_cond (z : SlotFormatCombinationsPerCell__ext0O__Type)
  : SlotFormatCombinationsPerCell__ext0O__cond z ->
  (seq_cond SlotFormatCombinationsPerCell__ext0O__list (SlotFormatCombinationsPerCell__ext0O__F1 z)).
intro H. unfold SlotFormatCombinationsPerCell__ext0O__cond in H. simpl. auto. Qed.
Lemma SlotFormatCombinationsPerCell__ext0O__F1F2_cond2 (z : SlotFormatCombinationsPerCell__ext0O__Type)
 : SlotFormatCombinationsPerCell__ext0O__F2 (SlotFormatCombinationsPerCell__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SlotFormatCombinationsPerCell__ext0O__F2F1_cond (y : seq_type SlotFormatCombinationsPerCell__ext0O__list)
  : seq_cond SlotFormatCombinationsPerCell__ext0O__list y ->
 (SlotFormatCombinationsPerCell__ext0O__cond (SlotFormatCombinationsPerCell__ext0O__F2 y)) /\  SlotFormatCombinationsPerCell__ext0O__F1 (SlotFormatCombinationsPerCell__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SlotFormatCombinationsPerCell__ext0O__cond. simpl in *. auto.
 - simpl. unfold SlotFormatCombinationsPerCell__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SlotFormatCombinationsPerCell__ext0O__Format : T_Format SlotFormatCombinationsPerCell__ext0O__Type SlotFormatCombinationsPerCell__ext0O__cond :=
        proj2_format  SlotFormatCombinationsPerCell__ext0O__cond SlotFormatCombinationsPerCell__ext0O__list__Format
    SlotFormatCombinationsPerCell__ext0O__F1 SlotFormatCombinationsPerCell__ext0O__F2 SlotFormatCombinationsPerCell__ext0O__F1F2_cond  SlotFormatCombinationsPerCell__ext0O__F1F2_cond2 SlotFormatCombinationsPerCell__ext0O__F2F1_cond.
Opaque SlotFormatCombinationsPerCell__ext0O__cond SlotFormatCombinationsPerCell__ext0O__Format.

Definition SlotFormatCombinationsPerCell__ext0__check_all_none (b : SlotFormatCombinationsPerCell__ext0O__Type) : bool :=
match b with 
  | make__SlotFormatCombinationsPerCell__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SlotFormatCombinationsPerCell__ext0__Format : T_Format SlotFormatCombinationsPerCell__ext0__Type SlotFormatCombinationsPerCell__ext0__cond :=
  restrict_add_format SlotFormatCombinationsPerCell__ext0__check_all_none SlotFormatCombinationsPerCell__ext0O__Format.

Opaque SlotFormatCombinationsPerCell__ext0__cond SlotFormatCombinationsPerCell__ext0__Format.


Definition SlotFormatCombinationsPerCell__root_Format_Type := Eval cbn in seq_format_prod SlotFormatCombinationsPerCell__root_list.
Definition SlotFormatCombinationsPerCell__root_Format_list : SlotFormatCombinationsPerCell__root_Format_Type :=
  (ServCellIndex__Format, (SubcarrierSpacing__Format, (SubcarrierSpacing__Format, (SlotFormatCombinationsPerCell__slotFormatCombinations__Format, (SlotFormatCombinationsPerCell__positionInDCI__Format, unit_format))))).

Definition SlotFormatCombinationsPerCell__ext_Format_Type := Eval cbn in get_formats SlotFormatCombinationsPerCell__ext_list.
Definition SlotFormatCombinationsPerCell__ext_Format_list : SlotFormatCombinationsPerCell__ext_Format_Type :=
  (SlotFormatCombinationsPerCell__ext0__Format, unit__Format).

Definition SlotFormatCombinationsPerCell__list_type : Set := (seq_type SlotFormatCombinationsPerCell__root_list) * (seq_ext_type SlotFormatCombinationsPerCell__ext_list).
Definition SlotFormatCombinationsPerCell__list_cond (z : SlotFormatCombinationsPerCell__list_type) : Prop :=
        (seq_cond SlotFormatCombinationsPerCell__root_list (fst z)) /\ (seq_ext_cond SlotFormatCombinationsPerCell__ext_list (snd z)).
Definition SlotFormatCombinationsPerCell__list_format : T_Format SlotFormatCombinationsPerCell__list_type SlotFormatCombinationsPerCell__list_cond :=
 (* Eval compute in *) seq_ext_format SlotFormatCombinationsPerCell__root_list SlotFormatCombinationsPerCell__root_Format_list SlotFormatCombinationsPerCell__ext_list SlotFormatCombinationsPerCell__ext_Format_list.

Opaque SlotFormatCombinationsPerCell__list_format.
Definition SlotFormatCombinationsPerCell__F1 (z : SlotFormatCombinationsPerCell__Type) : SlotFormatCombinationsPerCell__list_type :=
  (((SlotFormatCombinationsPerCell__servingCellId z, (SlotFormatCombinationsPerCell__subcarrierSpacing z, (SlotFormatCombinationsPerCell__subcarrierSpacing2 z, (SlotFormatCombinationsPerCell__slotFormatCombinations z, (SlotFormatCombinationsPerCell__positionInDCI z, tt)))))), (
(SlotFormatCombinationsPerCell__ext0 z, tt))).
Definition SlotFormatCombinationsPerCell__F2 (y : SlotFormatCombinationsPerCell__list_type) : SlotFormatCombinationsPerCell__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, _))=>
    make__SlotFormatCombinationsPerCell__Type j0 j1 j2 j3 j4 i0
  end.
Definition SlotFormatCombinationsPerCell__helper1 : (forall a : SlotFormatCombinationsPerCell__Type, SlotFormatCombinationsPerCell__cond a -> SlotFormatCombinationsPerCell__list_cond (SlotFormatCombinationsPerCell__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SlotFormatCombinationsPerCell__helper2 : (forall a : SlotFormatCombinationsPerCell__Type, SlotFormatCombinationsPerCell__F2 (SlotFormatCombinationsPerCell__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SlotFormatCombinationsPerCell__helper3 : (forall b : SlotFormatCombinationsPerCell__list_type, SlotFormatCombinationsPerCell__list_cond b -> SlotFormatCombinationsPerCell__cond (SlotFormatCombinationsPerCell__F2 b) /\ SlotFormatCombinationsPerCell__F1 (SlotFormatCombinationsPerCell__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SlotFormatCombinationsPerCell__cond, SlotFormatCombinationsPerCell__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SlotFormatCombinationsPerCell__Format : T_Format SlotFormatCombinationsPerCell__Type SlotFormatCombinationsPerCell__cond :=
 proj2_format SlotFormatCombinationsPerCell__cond SlotFormatCombinationsPerCell__list_format  SlotFormatCombinationsPerCell__F1 SlotFormatCombinationsPerCell__F2 SlotFormatCombinationsPerCell__helper1 SlotFormatCombinationsPerCell__helper2 SlotFormatCombinationsPerCell__helper3.

Opaque SlotFormatCombinationsPerCell__cond SlotFormatCombinationsPerCell__Format.

