Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Lemma CFRA_SSB_Resource__ra_PreambleIndex__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma CFRA_SSB_Resource__ra_PreambleIndex__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA_SSB_Resource__ra_PreambleIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA_SSB_Resource__ra_PreambleIndex__Type := Z.
Definition CFRA_SSB_Resource__ra_PreambleIndex__cond := (fun z => (0 <= z <= 63)%Z).
Lemma CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__helper1 : (0 <= 3071)%Z.  lia. Qed.
Lemma CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__helper2 : to_bit_sz (Z.to_nat (3071 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3071 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__Type := Z.
Definition CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__cond := (fun z => (0 <= z <= 3071)%Z).
Record CFRA_SSB_Resource__ext0O__Type : Set :=
  make__CFRA_SSB_Resource__ext0O__Type {
    CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16 : option Z ;
}.
Definition CFRA_SSB_Resource__ext0O__list := (
 Opt Z CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__cond ::
 nil).
Definition CFRA_SSB_Resource__ext0O__cond z := 
  opt_cond CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__cond (CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16 z) /\
  True.

Definition CFRA_SSB_Resource__ext0__Type := CFRA_SSB_Resource__ext0O__Type.
Definition CFRA_SSB_Resource__ext0__cond := CFRA_SSB_Resource__ext0O__cond.

Record CFRA_SSB_Resource__Type : Set :=
  make__CFRA_SSB_Resource__Type {
    CFRA_SSB_Resource__ssb : SSB_Index__Type ;
    CFRA_SSB_Resource__ra_PreambleIndex : Z ;
    CFRA_SSB_Resource__ext0 : option CFRA_SSB_Resource__ext0__Type ;
}.
Definition CFRA_SSB_Resource__root_list : list seq_elem := (
 Nor SSB_Index__Type SSB_Index__cond ::
 Nor Z CFRA_SSB_Resource__ra_PreambleIndex__cond ::
 nil).
Definition CFRA_SSB_Resource__ext_list : list typ := (
  typ_cons CFRA_SSB_Resource__ext0__Type CFRA_SSB_Resource__ext0__cond ::
  nil).
Definition CFRA_SSB_Resource__cond (z : CFRA_SSB_Resource__Type) := 
(  SSB_Index__cond (CFRA_SSB_Resource__ssb z) /\
  CFRA_SSB_Resource__ra_PreambleIndex__cond (CFRA_SSB_Resource__ra_PreambleIndex z) /\
  True) /\ 
(  opt_cond CFRA_SSB_Resource__ext0__cond (CFRA_SSB_Resource__ext0 z) /\
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
Definition CFRA_SSB_Resource__ra_PreambleIndex__Format : T_Format Z CFRA_SSB_Resource__ra_PreambleIndex__cond :=
 ranged_int_format (0) (63) CFRA_SSB_Resource__ra_PreambleIndex__helper1 CFRA_SSB_Resource__ra_PreambleIndex__helper2.

Opaque CFRA_SSB_Resource__ra_PreambleIndex__cond CFRA_SSB_Resource__ra_PreambleIndex__Format.

Definition CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__Format : T_Format Z CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__cond :=
 ranged_int_format (0) (3071) CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__helper1 CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__helper2.

Opaque CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__cond CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__Format.


Definition CFRA_SSB_Resource__ext0O__Format_Type := Eval cbn in seq_format_prod CFRA_SSB_Resource__ext0O__list.
Definition CFRA_SSB_Resource__ext0O__Format_list : CFRA_SSB_Resource__ext0O__Format_Type :=
  (CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16__Format, unit_format).
Definition CFRA_SSB_Resource__ext0O__list__Format := (*Eval compute in *) seq_format CFRA_SSB_Resource__ext0O__list CFRA_SSB_Resource__ext0O__Format_list.
Definition CFRA_SSB_Resource__ext0O__F1 z :=
  (CFRA_SSB_Resource__ext0O__msgA_PUSCH_Resource_Index_r16 z, tt).
Definition CFRA_SSB_Resource__ext0O__F2 (y : seq_type CFRA_SSB_Resource__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CFRA_SSB_Resource__ext0O__Type i0
  end.
Lemma CFRA_SSB_Resource__ext0O__F1F2_cond (z : CFRA_SSB_Resource__ext0O__Type)
  : CFRA_SSB_Resource__ext0O__cond z ->
  (seq_cond CFRA_SSB_Resource__ext0O__list (CFRA_SSB_Resource__ext0O__F1 z)).
intro H. unfold CFRA_SSB_Resource__ext0O__cond in H. simpl. auto. Qed.
Lemma CFRA_SSB_Resource__ext0O__F1F2_cond2 (z : CFRA_SSB_Resource__ext0O__Type)
 : CFRA_SSB_Resource__ext0O__F2 (CFRA_SSB_Resource__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFRA_SSB_Resource__ext0O__F2F1_cond (y : seq_type CFRA_SSB_Resource__ext0O__list)
  : seq_cond CFRA_SSB_Resource__ext0O__list y ->
 (CFRA_SSB_Resource__ext0O__cond (CFRA_SSB_Resource__ext0O__F2 y)) /\  CFRA_SSB_Resource__ext0O__F1 (CFRA_SSB_Resource__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFRA_SSB_Resource__ext0O__cond. simpl in *. auto.
 - simpl. unfold CFRA_SSB_Resource__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFRA_SSB_Resource__ext0O__Format : T_Format CFRA_SSB_Resource__ext0O__Type CFRA_SSB_Resource__ext0O__cond :=
        proj2_format  CFRA_SSB_Resource__ext0O__cond CFRA_SSB_Resource__ext0O__list__Format
    CFRA_SSB_Resource__ext0O__F1 CFRA_SSB_Resource__ext0O__F2 CFRA_SSB_Resource__ext0O__F1F2_cond  CFRA_SSB_Resource__ext0O__F1F2_cond2 CFRA_SSB_Resource__ext0O__F2F1_cond.
Opaque CFRA_SSB_Resource__ext0O__cond CFRA_SSB_Resource__ext0O__Format.

Definition CFRA_SSB_Resource__ext0__check_all_none (b : CFRA_SSB_Resource__ext0O__Type) : bool :=
match b with 
  | make__CFRA_SSB_Resource__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CFRA_SSB_Resource__ext0__Format : T_Format CFRA_SSB_Resource__ext0__Type CFRA_SSB_Resource__ext0__cond :=
  restrict_add_format CFRA_SSB_Resource__ext0__check_all_none CFRA_SSB_Resource__ext0O__Format.

Opaque CFRA_SSB_Resource__ext0__cond CFRA_SSB_Resource__ext0__Format.


Definition CFRA_SSB_Resource__root_Format_Type := Eval cbn in seq_format_prod CFRA_SSB_Resource__root_list.
Definition CFRA_SSB_Resource__root_Format_list : CFRA_SSB_Resource__root_Format_Type :=
  (SSB_Index__Format, (CFRA_SSB_Resource__ra_PreambleIndex__Format, unit_format)).

Definition CFRA_SSB_Resource__ext_Format_Type := Eval cbn in get_formats CFRA_SSB_Resource__ext_list.
Definition CFRA_SSB_Resource__ext_Format_list : CFRA_SSB_Resource__ext_Format_Type :=
  (CFRA_SSB_Resource__ext0__Format, unit__Format).

Definition CFRA_SSB_Resource__list_type : Set := (seq_type CFRA_SSB_Resource__root_list) * (seq_ext_type CFRA_SSB_Resource__ext_list).
Definition CFRA_SSB_Resource__list_cond (z : CFRA_SSB_Resource__list_type) : Prop :=
        (seq_cond CFRA_SSB_Resource__root_list (fst z)) /\ (seq_ext_cond CFRA_SSB_Resource__ext_list (snd z)).
Definition CFRA_SSB_Resource__list_format : T_Format CFRA_SSB_Resource__list_type CFRA_SSB_Resource__list_cond :=
 (* Eval compute in *) seq_ext_format CFRA_SSB_Resource__root_list CFRA_SSB_Resource__root_Format_list CFRA_SSB_Resource__ext_list CFRA_SSB_Resource__ext_Format_list.

Opaque CFRA_SSB_Resource__list_format.
Definition CFRA_SSB_Resource__F1 (z : CFRA_SSB_Resource__Type) : CFRA_SSB_Resource__list_type :=
  (((CFRA_SSB_Resource__ssb z, (CFRA_SSB_Resource__ra_PreambleIndex z, tt))), (
(CFRA_SSB_Resource__ext0 z, tt))).
Definition CFRA_SSB_Resource__F2 (y : CFRA_SSB_Resource__list_type) : CFRA_SSB_Resource__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__CFRA_SSB_Resource__Type j0 j1 i0
  end.
Definition CFRA_SSB_Resource__helper1 : (forall a : CFRA_SSB_Resource__Type, CFRA_SSB_Resource__cond a -> CFRA_SSB_Resource__list_cond (CFRA_SSB_Resource__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CFRA_SSB_Resource__helper2 : (forall a : CFRA_SSB_Resource__Type, CFRA_SSB_Resource__F2 (CFRA_SSB_Resource__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CFRA_SSB_Resource__helper3 : (forall b : CFRA_SSB_Resource__list_type, CFRA_SSB_Resource__list_cond b -> CFRA_SSB_Resource__cond (CFRA_SSB_Resource__F2 b) /\ CFRA_SSB_Resource__F1 (CFRA_SSB_Resource__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CFRA_SSB_Resource__cond, CFRA_SSB_Resource__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CFRA_SSB_Resource__Format : T_Format CFRA_SSB_Resource__Type CFRA_SSB_Resource__cond :=
 proj2_format CFRA_SSB_Resource__cond CFRA_SSB_Resource__list_format  CFRA_SSB_Resource__F1 CFRA_SSB_Resource__F2 CFRA_SSB_Resource__helper1 CFRA_SSB_Resource__helper2 CFRA_SSB_Resource__helper3.

Opaque CFRA_SSB_Resource__cond CFRA_SSB_Resource__Format.

