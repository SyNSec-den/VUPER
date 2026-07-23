Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_RS_Index.

Opaque CSI_RS_Index__cond CSI_RS_Index__Format.

Lemma CFRA_CSIRS_Resource__ra_OccasionList__seq_of__helper1 : (0 <= maxRA_Occasions_1)%Z. unfold maxRA_Occasions_1.
 lia. Qed.
Lemma CFRA_CSIRS_Resource__ra_OccasionList__seq_of__helper2 : to_bit_sz (Z.to_nat (maxRA_Occasions_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxRA_Occasions_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA_CSIRS_Resource__ra_OccasionList__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA_CSIRS_Resource__ra_OccasionList__seq_of__Type := Z.
Definition CFRA_CSIRS_Resource__ra_OccasionList__seq_of__cond := (fun z => (0 <= z <= maxRA_Occasions_1)%Z).
Definition CFRA_CSIRS_Resource__ra_OccasionList__Type := list Z.

Lemma CFRA_CSIRS_Resource__ra_OccasionList__helper1 : (0 <= 1 <= maxRA_OccasionsPerCSIRS)%Z. unfold maxRA_OccasionsPerCSIRS.
 lia. Qed.
Lemma CFRA_CSIRS_Resource__ra_OccasionList__helper2 : to_bit_sz (Z.to_nat (maxRA_OccasionsPerCSIRS - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxRA_OccasionsPerCSIRS - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA_CSIRS_Resource__ra_OccasionList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA_CSIRS_Resource__ra_OccasionList__cond (z : CFRA_CSIRS_Resource__ra_OccasionList__Type) :=  (1 <= Z.of_nat (length z) <= maxRA_OccasionsPerCSIRS)%Z /\ (list_and CFRA_CSIRS_Resource__ra_OccasionList__seq_of__cond z) .

Lemma CFRA_CSIRS_Resource__ra_PreambleIndex__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma CFRA_CSIRS_Resource__ra_PreambleIndex__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA_CSIRS_Resource__ra_PreambleIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA_CSIRS_Resource__ra_PreambleIndex__Type := Z.
Definition CFRA_CSIRS_Resource__ra_PreambleIndex__cond := (fun z => (0 <= z <= 63)%Z).
Record CFRA_CSIRS_Resource__Type : Set :=
  make__CFRA_CSIRS_Resource__Type {
    CFRA_CSIRS_Resource__csi_RS : CSI_RS_Index__Type ;
    CFRA_CSIRS_Resource__ra_OccasionList : CFRA_CSIRS_Resource__ra_OccasionList__Type ;
    CFRA_CSIRS_Resource__ra_PreambleIndex : Z ;
}.
Definition CFRA_CSIRS_Resource__root_list : list seq_elem := (
 Nor CSI_RS_Index__Type CSI_RS_Index__cond ::
 Nor CFRA_CSIRS_Resource__ra_OccasionList__Type CFRA_CSIRS_Resource__ra_OccasionList__cond ::
 Nor Z CFRA_CSIRS_Resource__ra_PreambleIndex__cond ::
 nil).
Definition CFRA_CSIRS_Resource__ext_list : list typ := (
  nil).
Definition CFRA_CSIRS_Resource__cond (z : CFRA_CSIRS_Resource__Type) := 
(  CSI_RS_Index__cond (CFRA_CSIRS_Resource__csi_RS z) /\
  CFRA_CSIRS_Resource__ra_OccasionList__cond (CFRA_CSIRS_Resource__ra_OccasionList z) /\
  CFRA_CSIRS_Resource__ra_PreambleIndex__cond (CFRA_CSIRS_Resource__ra_PreambleIndex z) /\
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
Definition CFRA_CSIRS_Resource__ra_OccasionList__seq_of__Format : T_Format Z CFRA_CSIRS_Resource__ra_OccasionList__seq_of__cond :=
 ranged_int_format (0) (maxRA_Occasions_1) CFRA_CSIRS_Resource__ra_OccasionList__seq_of__helper1 CFRA_CSIRS_Resource__ra_OccasionList__seq_of__helper2.

Opaque CFRA_CSIRS_Resource__ra_OccasionList__seq_of__cond CFRA_CSIRS_Resource__ra_OccasionList__seq_of__Format.

Definition CFRA_CSIRS_Resource__ra_OccasionList__Format : T_Format CFRA_CSIRS_Resource__ra_OccasionList__Type CFRA_CSIRS_Resource__ra_OccasionList__cond := seq_of_format CFRA_CSIRS_Resource__ra_OccasionList__seq_of__Format 1 maxRA_OccasionsPerCSIRS CFRA_CSIRS_Resource__ra_OccasionList__helper1 CFRA_CSIRS_Resource__ra_OccasionList__helper2.

Opaque CFRA_CSIRS_Resource__ra_OccasionList__cond CFRA_CSIRS_Resource__ra_OccasionList__Format.

Definition CFRA_CSIRS_Resource__ra_PreambleIndex__Format : T_Format Z CFRA_CSIRS_Resource__ra_PreambleIndex__cond :=
 ranged_int_format (0) (63) CFRA_CSIRS_Resource__ra_PreambleIndex__helper1 CFRA_CSIRS_Resource__ra_PreambleIndex__helper2.

Opaque CFRA_CSIRS_Resource__ra_PreambleIndex__cond CFRA_CSIRS_Resource__ra_PreambleIndex__Format.


Definition CFRA_CSIRS_Resource__root_Format_Type := Eval cbn in seq_format_prod CFRA_CSIRS_Resource__root_list.
Definition CFRA_CSIRS_Resource__root_Format_list : CFRA_CSIRS_Resource__root_Format_Type :=
  (CSI_RS_Index__Format, (CFRA_CSIRS_Resource__ra_OccasionList__Format, (CFRA_CSIRS_Resource__ra_PreambleIndex__Format, unit_format))).

Definition CFRA_CSIRS_Resource__ext_Format_Type := Eval cbn in get_formats CFRA_CSIRS_Resource__ext_list.
Definition CFRA_CSIRS_Resource__ext_Format_list : CFRA_CSIRS_Resource__ext_Format_Type :=
  unit__Format.

Definition CFRA_CSIRS_Resource__list_type : Set := (seq_type CFRA_CSIRS_Resource__root_list) * (seq_ext_type CFRA_CSIRS_Resource__ext_list).
Definition CFRA_CSIRS_Resource__list_cond (z : CFRA_CSIRS_Resource__list_type) : Prop :=
        (seq_cond CFRA_CSIRS_Resource__root_list (fst z)) /\ (seq_ext_cond CFRA_CSIRS_Resource__ext_list (snd z)).
Definition CFRA_CSIRS_Resource__list_format : T_Format CFRA_CSIRS_Resource__list_type CFRA_CSIRS_Resource__list_cond :=
 (* Eval compute in *) seq_ext_format CFRA_CSIRS_Resource__root_list CFRA_CSIRS_Resource__root_Format_list CFRA_CSIRS_Resource__ext_list CFRA_CSIRS_Resource__ext_Format_list.

Opaque CFRA_CSIRS_Resource__list_format.
Definition CFRA_CSIRS_Resource__F1 (z : CFRA_CSIRS_Resource__Type) : CFRA_CSIRS_Resource__list_type :=
  (((CFRA_CSIRS_Resource__csi_RS z, (CFRA_CSIRS_Resource__ra_OccasionList z, (CFRA_CSIRS_Resource__ra_PreambleIndex z, tt)))), (
tt)).
Definition CFRA_CSIRS_Resource__F2 (y : CFRA_CSIRS_Resource__list_type) : CFRA_CSIRS_Resource__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__CFRA_CSIRS_Resource__Type j0 j1 j2
  end.
Definition CFRA_CSIRS_Resource__helper1 : (forall a : CFRA_CSIRS_Resource__Type, CFRA_CSIRS_Resource__cond a -> CFRA_CSIRS_Resource__list_cond (CFRA_CSIRS_Resource__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CFRA_CSIRS_Resource__helper2 : (forall a : CFRA_CSIRS_Resource__Type, CFRA_CSIRS_Resource__F2 (CFRA_CSIRS_Resource__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CFRA_CSIRS_Resource__helper3 : (forall b : CFRA_CSIRS_Resource__list_type, CFRA_CSIRS_Resource__list_cond b -> CFRA_CSIRS_Resource__cond (CFRA_CSIRS_Resource__F2 b) /\ CFRA_CSIRS_Resource__F1 (CFRA_CSIRS_Resource__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CFRA_CSIRS_Resource__cond, CFRA_CSIRS_Resource__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CFRA_CSIRS_Resource__Format : T_Format CFRA_CSIRS_Resource__Type CFRA_CSIRS_Resource__cond :=
 proj2_format CFRA_CSIRS_Resource__cond CFRA_CSIRS_Resource__list_format  CFRA_CSIRS_Resource__F1 CFRA_CSIRS_Resource__F2 CFRA_CSIRS_Resource__helper1 CFRA_CSIRS_Resource__helper2 CFRA_CSIRS_Resource__helper3.

Opaque CFRA_CSIRS_Resource__cond CFRA_CSIRS_Resource__Format.

