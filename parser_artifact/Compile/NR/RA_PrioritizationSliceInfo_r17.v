Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NSAG_ID_r17.

Opaque NSAG_ID_r17__cond NSAG_ID_r17__Format.

Definition RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__Type := list NSAG_ID_r17__Type.

Lemma RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__helper1 : (0 <= 1 <= maxSliceInfo_r17)%Z. unfold maxSliceInfo_r17.
 lia. Qed.
Lemma RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__helper2 : to_bit_sz (Z.to_nat (maxSliceInfo_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSliceInfo_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__cond (z : RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxSliceInfo_r17)%Z /\ (list_and NSAG_ID_r17__cond z) .

Require Import NR.RA_Prioritization.

Opaque RA_Prioritization__cond RA_Prioritization__Format.

Record RA_PrioritizationSliceInfo_r17__Type : Set :=
  make__RA_PrioritizationSliceInfo_r17__Type {
    RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17 : RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__Type ;
    RA_PrioritizationSliceInfo_r17__ra_Prioritization_r17 : RA_Prioritization__Type ;
}.
Definition RA_PrioritizationSliceInfo_r17__root_list : list seq_elem := (
 Nor RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__Type RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__cond ::
 Nor RA_Prioritization__Type RA_Prioritization__cond ::
 nil).
Definition RA_PrioritizationSliceInfo_r17__ext_list : list typ := (
  nil).
Definition RA_PrioritizationSliceInfo_r17__cond (z : RA_PrioritizationSliceInfo_r17__Type) := 
(  RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__cond (RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17 z) /\
  RA_Prioritization__cond (RA_PrioritizationSliceInfo_r17__ra_Prioritization_r17 z) /\
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
Definition RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__Format : T_Format RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__Type RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__cond := seq_of_format NSAG_ID_r17__Format 1 maxSliceInfo_r17 RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__helper1 RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__helper2.

Opaque RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__cond RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__Format.


Definition RA_PrioritizationSliceInfo_r17__root_Format_Type := Eval cbn in seq_format_prod RA_PrioritizationSliceInfo_r17__root_list.
Definition RA_PrioritizationSliceInfo_r17__root_Format_list : RA_PrioritizationSliceInfo_r17__root_Format_Type :=
  (RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17__Format, (RA_Prioritization__Format, unit_format)).

Definition RA_PrioritizationSliceInfo_r17__ext_Format_Type := Eval cbn in get_formats RA_PrioritizationSliceInfo_r17__ext_list.
Definition RA_PrioritizationSliceInfo_r17__ext_Format_list : RA_PrioritizationSliceInfo_r17__ext_Format_Type :=
  unit__Format.

Definition RA_PrioritizationSliceInfo_r17__list_type : Set := (seq_type RA_PrioritizationSliceInfo_r17__root_list) * (seq_ext_type RA_PrioritizationSliceInfo_r17__ext_list).
Definition RA_PrioritizationSliceInfo_r17__list_cond (z : RA_PrioritizationSliceInfo_r17__list_type) : Prop :=
        (seq_cond RA_PrioritizationSliceInfo_r17__root_list (fst z)) /\ (seq_ext_cond RA_PrioritizationSliceInfo_r17__ext_list (snd z)).
Definition RA_PrioritizationSliceInfo_r17__list_format : T_Format RA_PrioritizationSliceInfo_r17__list_type RA_PrioritizationSliceInfo_r17__list_cond :=
 (* Eval compute in *) seq_ext_format RA_PrioritizationSliceInfo_r17__root_list RA_PrioritizationSliceInfo_r17__root_Format_list RA_PrioritizationSliceInfo_r17__ext_list RA_PrioritizationSliceInfo_r17__ext_Format_list.

Opaque RA_PrioritizationSliceInfo_r17__list_format.
Definition RA_PrioritizationSliceInfo_r17__F1 (z : RA_PrioritizationSliceInfo_r17__Type) : RA_PrioritizationSliceInfo_r17__list_type :=
  (((RA_PrioritizationSliceInfo_r17__nsag_ID_List_r17 z, (RA_PrioritizationSliceInfo_r17__ra_Prioritization_r17 z, tt))), (
tt)).
Definition RA_PrioritizationSliceInfo_r17__F2 (y : RA_PrioritizationSliceInfo_r17__list_type) : RA_PrioritizationSliceInfo_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__RA_PrioritizationSliceInfo_r17__Type j0 j1
  end.
Definition RA_PrioritizationSliceInfo_r17__helper1 : (forall a : RA_PrioritizationSliceInfo_r17__Type, RA_PrioritizationSliceInfo_r17__cond a -> RA_PrioritizationSliceInfo_r17__list_cond (RA_PrioritizationSliceInfo_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RA_PrioritizationSliceInfo_r17__helper2 : (forall a : RA_PrioritizationSliceInfo_r17__Type, RA_PrioritizationSliceInfo_r17__F2 (RA_PrioritizationSliceInfo_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RA_PrioritizationSliceInfo_r17__helper3 : (forall b : RA_PrioritizationSliceInfo_r17__list_type, RA_PrioritizationSliceInfo_r17__list_cond b -> RA_PrioritizationSliceInfo_r17__cond (RA_PrioritizationSliceInfo_r17__F2 b) /\ RA_PrioritizationSliceInfo_r17__F1 (RA_PrioritizationSliceInfo_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RA_PrioritizationSliceInfo_r17__cond, RA_PrioritizationSliceInfo_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RA_PrioritizationSliceInfo_r17__Format : T_Format RA_PrioritizationSliceInfo_r17__Type RA_PrioritizationSliceInfo_r17__cond :=
 proj2_format RA_PrioritizationSliceInfo_r17__cond RA_PrioritizationSliceInfo_r17__list_format  RA_PrioritizationSliceInfo_r17__F1 RA_PrioritizationSliceInfo_r17__F2 RA_PrioritizationSliceInfo_r17__helper1 RA_PrioritizationSliceInfo_r17__helper2 RA_PrioritizationSliceInfo_r17__helper3.

Opaque RA_PrioritizationSliceInfo_r17__cond RA_PrioritizationSliceInfo_r17__Format.

