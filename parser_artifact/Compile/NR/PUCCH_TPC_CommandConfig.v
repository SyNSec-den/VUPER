Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUCCH_TPC_CommandConfig__tpc_IndexPCell__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma PUCCH_TPC_CommandConfig__tpc_IndexPCell__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_TPC_CommandConfig__tpc_IndexPCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_TPC_CommandConfig__tpc_IndexPCell__Type := Z.
Definition PUCCH_TPC_CommandConfig__tpc_IndexPCell__cond := (fun z => (1 <= z <= 15)%Z).
Lemma PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__Type := Z.
Definition PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__cond := (fun z => (1 <= z <= 15)%Z).
Lemma PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__Type := Z.
Definition PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__cond := (fun z => (1 <= z <= 15)%Z).
Lemma PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__Type := Z.
Definition PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__cond := (fun z => (1 <= z <= 15)%Z).
Record PUCCH_TPC_CommandConfig__ext0O__Type : Set :=
  make__PUCCH_TPC_CommandConfig__ext0O__Type {
    PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17 : option Z ;
    PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17 : option Z ;
}.
Definition PUCCH_TPC_CommandConfig__ext0O__list := (
 Opt Z PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__cond ::
 Opt Z PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__cond ::
 nil).
Definition PUCCH_TPC_CommandConfig__ext0O__cond z := 
  opt_cond PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__cond (PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17 z) /\
  opt_cond PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__cond (PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17 z) /\
  True.

Definition PUCCH_TPC_CommandConfig__ext0__Type := PUCCH_TPC_CommandConfig__ext0O__Type.
Definition PUCCH_TPC_CommandConfig__ext0__cond := PUCCH_TPC_CommandConfig__ext0O__cond.

Record PUCCH_TPC_CommandConfig__Type : Set :=
  make__PUCCH_TPC_CommandConfig__Type {
    PUCCH_TPC_CommandConfig__tpc_IndexPCell : option Z ;
    PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell : option Z ;
    PUCCH_TPC_CommandConfig__ext0 : option PUCCH_TPC_CommandConfig__ext0__Type ;
}.
Definition PUCCH_TPC_CommandConfig__root_list : list seq_elem := (
 Opt Z PUCCH_TPC_CommandConfig__tpc_IndexPCell__cond ::
 Opt Z PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__cond ::
 nil).
Definition PUCCH_TPC_CommandConfig__ext_list : list typ := (
  typ_cons PUCCH_TPC_CommandConfig__ext0__Type PUCCH_TPC_CommandConfig__ext0__cond ::
  nil).
Definition PUCCH_TPC_CommandConfig__cond (z : PUCCH_TPC_CommandConfig__Type) := 
(  opt_cond PUCCH_TPC_CommandConfig__tpc_IndexPCell__cond (PUCCH_TPC_CommandConfig__tpc_IndexPCell z) /\
  opt_cond PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__cond (PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell z) /\
  True) /\ 
(  opt_cond PUCCH_TPC_CommandConfig__ext0__cond (PUCCH_TPC_CommandConfig__ext0 z) /\
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
Definition PUCCH_TPC_CommandConfig__tpc_IndexPCell__Format : T_Format Z PUCCH_TPC_CommandConfig__tpc_IndexPCell__cond :=
 ranged_int_format (1) (15) PUCCH_TPC_CommandConfig__tpc_IndexPCell__helper1 PUCCH_TPC_CommandConfig__tpc_IndexPCell__helper2.

Opaque PUCCH_TPC_CommandConfig__tpc_IndexPCell__cond PUCCH_TPC_CommandConfig__tpc_IndexPCell__Format.

Definition PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__Format : T_Format Z PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__cond :=
 ranged_int_format (1) (15) PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__helper1 PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__helper2.

Opaque PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__cond PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__Format.

Definition PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__Format : T_Format Z PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__cond :=
 ranged_int_format (1) (15) PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__helper1 PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__helper2.

Opaque PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__cond PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__Format.

Definition PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__Format : T_Format Z PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__cond :=
 ranged_int_format (1) (15) PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__helper1 PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__helper2.

Opaque PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__cond PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__Format.


Definition PUCCH_TPC_CommandConfig__ext0O__Format_Type := Eval cbn in seq_format_prod PUCCH_TPC_CommandConfig__ext0O__list.
Definition PUCCH_TPC_CommandConfig__ext0O__Format_list : PUCCH_TPC_CommandConfig__ext0O__Format_Type :=
  (PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17__Format, (PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17__Format, unit_format)).
Definition PUCCH_TPC_CommandConfig__ext0O__list__Format := (*Eval compute in *) seq_format PUCCH_TPC_CommandConfig__ext0O__list PUCCH_TPC_CommandConfig__ext0O__Format_list.
Definition PUCCH_TPC_CommandConfig__ext0O__F1 z :=
  (PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sSCell_r17 z, (PUCCH_TPC_CommandConfig__ext0O__tpc_IndexPUCCH_sScellSecondaryPUCCHgroup_r17 z, tt)).
Definition PUCCH_TPC_CommandConfig__ext0O__F2 (y : seq_type PUCCH_TPC_CommandConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUCCH_TPC_CommandConfig__ext0O__Type i0 i1
  end.
Lemma PUCCH_TPC_CommandConfig__ext0O__F1F2_cond (z : PUCCH_TPC_CommandConfig__ext0O__Type)
  : PUCCH_TPC_CommandConfig__ext0O__cond z ->
  (seq_cond PUCCH_TPC_CommandConfig__ext0O__list (PUCCH_TPC_CommandConfig__ext0O__F1 z)).
intro H. unfold PUCCH_TPC_CommandConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma PUCCH_TPC_CommandConfig__ext0O__F1F2_cond2 (z : PUCCH_TPC_CommandConfig__ext0O__Type)
 : PUCCH_TPC_CommandConfig__ext0O__F2 (PUCCH_TPC_CommandConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_TPC_CommandConfig__ext0O__F2F1_cond (y : seq_type PUCCH_TPC_CommandConfig__ext0O__list)
  : seq_cond PUCCH_TPC_CommandConfig__ext0O__list y ->
 (PUCCH_TPC_CommandConfig__ext0O__cond (PUCCH_TPC_CommandConfig__ext0O__F2 y)) /\  PUCCH_TPC_CommandConfig__ext0O__F1 (PUCCH_TPC_CommandConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_TPC_CommandConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUCCH_TPC_CommandConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_TPC_CommandConfig__ext0O__Format : T_Format PUCCH_TPC_CommandConfig__ext0O__Type PUCCH_TPC_CommandConfig__ext0O__cond :=
        proj2_format  PUCCH_TPC_CommandConfig__ext0O__cond PUCCH_TPC_CommandConfig__ext0O__list__Format
    PUCCH_TPC_CommandConfig__ext0O__F1 PUCCH_TPC_CommandConfig__ext0O__F2 PUCCH_TPC_CommandConfig__ext0O__F1F2_cond  PUCCH_TPC_CommandConfig__ext0O__F1F2_cond2 PUCCH_TPC_CommandConfig__ext0O__F2F1_cond.
Opaque PUCCH_TPC_CommandConfig__ext0O__cond PUCCH_TPC_CommandConfig__ext0O__Format.

Definition PUCCH_TPC_CommandConfig__ext0__check_all_none (b : PUCCH_TPC_CommandConfig__ext0O__Type) : bool :=
match b with 
  | make__PUCCH_TPC_CommandConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition PUCCH_TPC_CommandConfig__ext0__Format : T_Format PUCCH_TPC_CommandConfig__ext0__Type PUCCH_TPC_CommandConfig__ext0__cond :=
  restrict_add_format PUCCH_TPC_CommandConfig__ext0__check_all_none PUCCH_TPC_CommandConfig__ext0O__Format.

Opaque PUCCH_TPC_CommandConfig__ext0__cond PUCCH_TPC_CommandConfig__ext0__Format.


Definition PUCCH_TPC_CommandConfig__root_Format_Type := Eval cbn in seq_format_prod PUCCH_TPC_CommandConfig__root_list.
Definition PUCCH_TPC_CommandConfig__root_Format_list : PUCCH_TPC_CommandConfig__root_Format_Type :=
  (PUCCH_TPC_CommandConfig__tpc_IndexPCell__Format, (PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell__Format, unit_format)).

Definition PUCCH_TPC_CommandConfig__ext_Format_Type := Eval cbn in get_formats PUCCH_TPC_CommandConfig__ext_list.
Definition PUCCH_TPC_CommandConfig__ext_Format_list : PUCCH_TPC_CommandConfig__ext_Format_Type :=
  (PUCCH_TPC_CommandConfig__ext0__Format, unit__Format).

Definition PUCCH_TPC_CommandConfig__list_type : Set := (seq_type PUCCH_TPC_CommandConfig__root_list) * (seq_ext_type PUCCH_TPC_CommandConfig__ext_list).
Definition PUCCH_TPC_CommandConfig__list_cond (z : PUCCH_TPC_CommandConfig__list_type) : Prop :=
        (seq_cond PUCCH_TPC_CommandConfig__root_list (fst z)) /\ (seq_ext_cond PUCCH_TPC_CommandConfig__ext_list (snd z)).
Definition PUCCH_TPC_CommandConfig__list_format : T_Format PUCCH_TPC_CommandConfig__list_type PUCCH_TPC_CommandConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PUCCH_TPC_CommandConfig__root_list PUCCH_TPC_CommandConfig__root_Format_list PUCCH_TPC_CommandConfig__ext_list PUCCH_TPC_CommandConfig__ext_Format_list.

Opaque PUCCH_TPC_CommandConfig__list_format.
Definition PUCCH_TPC_CommandConfig__F1 (z : PUCCH_TPC_CommandConfig__Type) : PUCCH_TPC_CommandConfig__list_type :=
  (((PUCCH_TPC_CommandConfig__tpc_IndexPCell z, (PUCCH_TPC_CommandConfig__tpc_IndexPUCCH_SCell z, tt))), (
(PUCCH_TPC_CommandConfig__ext0 z, tt))).
Definition PUCCH_TPC_CommandConfig__F2 (y : PUCCH_TPC_CommandConfig__list_type) : PUCCH_TPC_CommandConfig__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__PUCCH_TPC_CommandConfig__Type j0 j1 i0
  end.
Definition PUCCH_TPC_CommandConfig__helper1 : (forall a : PUCCH_TPC_CommandConfig__Type, PUCCH_TPC_CommandConfig__cond a -> PUCCH_TPC_CommandConfig__list_cond (PUCCH_TPC_CommandConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUCCH_TPC_CommandConfig__helper2 : (forall a : PUCCH_TPC_CommandConfig__Type, PUCCH_TPC_CommandConfig__F2 (PUCCH_TPC_CommandConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUCCH_TPC_CommandConfig__helper3 : (forall b : PUCCH_TPC_CommandConfig__list_type, PUCCH_TPC_CommandConfig__list_cond b -> PUCCH_TPC_CommandConfig__cond (PUCCH_TPC_CommandConfig__F2 b) /\ PUCCH_TPC_CommandConfig__F1 (PUCCH_TPC_CommandConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUCCH_TPC_CommandConfig__cond, PUCCH_TPC_CommandConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUCCH_TPC_CommandConfig__Format : T_Format PUCCH_TPC_CommandConfig__Type PUCCH_TPC_CommandConfig__cond :=
 proj2_format PUCCH_TPC_CommandConfig__cond PUCCH_TPC_CommandConfig__list_format  PUCCH_TPC_CommandConfig__F1 PUCCH_TPC_CommandConfig__F2 PUCCH_TPC_CommandConfig__helper1 PUCCH_TPC_CommandConfig__helper2 PUCCH_TPC_CommandConfig__helper3.

Opaque PUCCH_TPC_CommandConfig__cond PUCCH_TPC_CommandConfig__Format.

