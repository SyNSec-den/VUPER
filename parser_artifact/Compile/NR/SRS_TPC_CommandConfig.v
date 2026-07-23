Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SRS_TPC_CommandConfig__startingBitOfFormat2_3__helper1 : (1 <= 31)%Z.  lia. Qed.
Lemma SRS_TPC_CommandConfig__startingBitOfFormat2_3__helper2 : to_bit_sz (Z.to_nat (31 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_TPC_CommandConfig__startingBitOfFormat2_3__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_TPC_CommandConfig__startingBitOfFormat2_3__Type := Z.
Definition SRS_TPC_CommandConfig__startingBitOfFormat2_3__cond := (fun z => (1 <= z <= 31)%Z).
Lemma SRS_TPC_CommandConfig__fieldTypeFormat2_3__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma SRS_TPC_CommandConfig__fieldTypeFormat2_3__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_TPC_CommandConfig__fieldTypeFormat2_3__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_TPC_CommandConfig__fieldTypeFormat2_3__Type := Z.
Definition SRS_TPC_CommandConfig__fieldTypeFormat2_3__cond := (fun z => (0 <= z <= 1)%Z).
Lemma SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__helper1 : (1 <= 31)%Z.  lia. Qed.
Lemma SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__helper2 : to_bit_sz (Z.to_nat (31 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__Type := Z.
Definition SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__cond := (fun z => (1 <= z <= 31)%Z).
Record SRS_TPC_CommandConfig__ext0O__Type : Set :=
  make__SRS_TPC_CommandConfig__ext0O__Type {
    SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL : option Z ;
}.
Definition SRS_TPC_CommandConfig__ext0O__list := (
 Opt Z SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__cond ::
 nil).
Definition SRS_TPC_CommandConfig__ext0O__cond z := 
  opt_cond SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__cond (SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL z) /\
  True.

Definition SRS_TPC_CommandConfig__ext0__Type := SRS_TPC_CommandConfig__ext0O__Type.
Definition SRS_TPC_CommandConfig__ext0__cond := SRS_TPC_CommandConfig__ext0O__cond.

Record SRS_TPC_CommandConfig__Type : Set :=
  make__SRS_TPC_CommandConfig__Type {
    SRS_TPC_CommandConfig__startingBitOfFormat2_3 : option Z ;
    SRS_TPC_CommandConfig__fieldTypeFormat2_3 : option Z ;
    SRS_TPC_CommandConfig__ext0 : option SRS_TPC_CommandConfig__ext0__Type ;
}.
Definition SRS_TPC_CommandConfig__root_list : list seq_elem := (
 Opt Z SRS_TPC_CommandConfig__startingBitOfFormat2_3__cond ::
 Opt Z SRS_TPC_CommandConfig__fieldTypeFormat2_3__cond ::
 nil).
Definition SRS_TPC_CommandConfig__ext_list : list typ := (
  typ_cons SRS_TPC_CommandConfig__ext0__Type SRS_TPC_CommandConfig__ext0__cond ::
  nil).
Definition SRS_TPC_CommandConfig__cond (z : SRS_TPC_CommandConfig__Type) := 
(  opt_cond SRS_TPC_CommandConfig__startingBitOfFormat2_3__cond (SRS_TPC_CommandConfig__startingBitOfFormat2_3 z) /\
  opt_cond SRS_TPC_CommandConfig__fieldTypeFormat2_3__cond (SRS_TPC_CommandConfig__fieldTypeFormat2_3 z) /\
  True) /\ 
(  opt_cond SRS_TPC_CommandConfig__ext0__cond (SRS_TPC_CommandConfig__ext0 z) /\
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
Definition SRS_TPC_CommandConfig__startingBitOfFormat2_3__Format : T_Format Z SRS_TPC_CommandConfig__startingBitOfFormat2_3__cond :=
 ranged_int_format (1) (31) SRS_TPC_CommandConfig__startingBitOfFormat2_3__helper1 SRS_TPC_CommandConfig__startingBitOfFormat2_3__helper2.

Opaque SRS_TPC_CommandConfig__startingBitOfFormat2_3__cond SRS_TPC_CommandConfig__startingBitOfFormat2_3__Format.

Definition SRS_TPC_CommandConfig__fieldTypeFormat2_3__Format : T_Format Z SRS_TPC_CommandConfig__fieldTypeFormat2_3__cond :=
 ranged_int_format (0) (1) SRS_TPC_CommandConfig__fieldTypeFormat2_3__helper1 SRS_TPC_CommandConfig__fieldTypeFormat2_3__helper2.

Opaque SRS_TPC_CommandConfig__fieldTypeFormat2_3__cond SRS_TPC_CommandConfig__fieldTypeFormat2_3__Format.

Definition SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__Format : T_Format Z SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__cond :=
 ranged_int_format (1) (31) SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__helper1 SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__helper2.

Opaque SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__cond SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__Format.


Definition SRS_TPC_CommandConfig__ext0O__Format_Type := Eval cbn in seq_format_prod SRS_TPC_CommandConfig__ext0O__list.
Definition SRS_TPC_CommandConfig__ext0O__Format_list : SRS_TPC_CommandConfig__ext0O__Format_Type :=
  (SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL__Format, unit_format).
Definition SRS_TPC_CommandConfig__ext0O__list__Format := (*Eval compute in *) seq_format SRS_TPC_CommandConfig__ext0O__list SRS_TPC_CommandConfig__ext0O__Format_list.
Definition SRS_TPC_CommandConfig__ext0O__F1 z :=
  (SRS_TPC_CommandConfig__ext0O__startingBitOfFormat2_3SUL z, tt).
Definition SRS_TPC_CommandConfig__ext0O__F2 (y : seq_type SRS_TPC_CommandConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SRS_TPC_CommandConfig__ext0O__Type i0
  end.
Lemma SRS_TPC_CommandConfig__ext0O__F1F2_cond (z : SRS_TPC_CommandConfig__ext0O__Type)
  : SRS_TPC_CommandConfig__ext0O__cond z ->
  (seq_cond SRS_TPC_CommandConfig__ext0O__list (SRS_TPC_CommandConfig__ext0O__F1 z)).
intro H. unfold SRS_TPC_CommandConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma SRS_TPC_CommandConfig__ext0O__F1F2_cond2 (z : SRS_TPC_CommandConfig__ext0O__Type)
 : SRS_TPC_CommandConfig__ext0O__F2 (SRS_TPC_CommandConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_TPC_CommandConfig__ext0O__F2F1_cond (y : seq_type SRS_TPC_CommandConfig__ext0O__list)
  : seq_cond SRS_TPC_CommandConfig__ext0O__list y ->
 (SRS_TPC_CommandConfig__ext0O__cond (SRS_TPC_CommandConfig__ext0O__F2 y)) /\  SRS_TPC_CommandConfig__ext0O__F1 (SRS_TPC_CommandConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_TPC_CommandConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold SRS_TPC_CommandConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_TPC_CommandConfig__ext0O__Format : T_Format SRS_TPC_CommandConfig__ext0O__Type SRS_TPC_CommandConfig__ext0O__cond :=
        proj2_format  SRS_TPC_CommandConfig__ext0O__cond SRS_TPC_CommandConfig__ext0O__list__Format
    SRS_TPC_CommandConfig__ext0O__F1 SRS_TPC_CommandConfig__ext0O__F2 SRS_TPC_CommandConfig__ext0O__F1F2_cond  SRS_TPC_CommandConfig__ext0O__F1F2_cond2 SRS_TPC_CommandConfig__ext0O__F2F1_cond.
Opaque SRS_TPC_CommandConfig__ext0O__cond SRS_TPC_CommandConfig__ext0O__Format.

Definition SRS_TPC_CommandConfig__ext0__check_all_none (b : SRS_TPC_CommandConfig__ext0O__Type) : bool :=
match b with 
  | make__SRS_TPC_CommandConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SRS_TPC_CommandConfig__ext0__Format : T_Format SRS_TPC_CommandConfig__ext0__Type SRS_TPC_CommandConfig__ext0__cond :=
  restrict_add_format SRS_TPC_CommandConfig__ext0__check_all_none SRS_TPC_CommandConfig__ext0O__Format.

Opaque SRS_TPC_CommandConfig__ext0__cond SRS_TPC_CommandConfig__ext0__Format.


Definition SRS_TPC_CommandConfig__root_Format_Type := Eval cbn in seq_format_prod SRS_TPC_CommandConfig__root_list.
Definition SRS_TPC_CommandConfig__root_Format_list : SRS_TPC_CommandConfig__root_Format_Type :=
  (SRS_TPC_CommandConfig__startingBitOfFormat2_3__Format, (SRS_TPC_CommandConfig__fieldTypeFormat2_3__Format, unit_format)).

Definition SRS_TPC_CommandConfig__ext_Format_Type := Eval cbn in get_formats SRS_TPC_CommandConfig__ext_list.
Definition SRS_TPC_CommandConfig__ext_Format_list : SRS_TPC_CommandConfig__ext_Format_Type :=
  (SRS_TPC_CommandConfig__ext0__Format, unit__Format).

Definition SRS_TPC_CommandConfig__list_type : Set := (seq_type SRS_TPC_CommandConfig__root_list) * (seq_ext_type SRS_TPC_CommandConfig__ext_list).
Definition SRS_TPC_CommandConfig__list_cond (z : SRS_TPC_CommandConfig__list_type) : Prop :=
        (seq_cond SRS_TPC_CommandConfig__root_list (fst z)) /\ (seq_ext_cond SRS_TPC_CommandConfig__ext_list (snd z)).
Definition SRS_TPC_CommandConfig__list_format : T_Format SRS_TPC_CommandConfig__list_type SRS_TPC_CommandConfig__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_TPC_CommandConfig__root_list SRS_TPC_CommandConfig__root_Format_list SRS_TPC_CommandConfig__ext_list SRS_TPC_CommandConfig__ext_Format_list.

Opaque SRS_TPC_CommandConfig__list_format.
Definition SRS_TPC_CommandConfig__F1 (z : SRS_TPC_CommandConfig__Type) : SRS_TPC_CommandConfig__list_type :=
  (((SRS_TPC_CommandConfig__startingBitOfFormat2_3 z, (SRS_TPC_CommandConfig__fieldTypeFormat2_3 z, tt))), (
(SRS_TPC_CommandConfig__ext0 z, tt))).
Definition SRS_TPC_CommandConfig__F2 (y : SRS_TPC_CommandConfig__list_type) : SRS_TPC_CommandConfig__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__SRS_TPC_CommandConfig__Type j0 j1 i0
  end.
Definition SRS_TPC_CommandConfig__helper1 : (forall a : SRS_TPC_CommandConfig__Type, SRS_TPC_CommandConfig__cond a -> SRS_TPC_CommandConfig__list_cond (SRS_TPC_CommandConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_TPC_CommandConfig__helper2 : (forall a : SRS_TPC_CommandConfig__Type, SRS_TPC_CommandConfig__F2 (SRS_TPC_CommandConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_TPC_CommandConfig__helper3 : (forall b : SRS_TPC_CommandConfig__list_type, SRS_TPC_CommandConfig__list_cond b -> SRS_TPC_CommandConfig__cond (SRS_TPC_CommandConfig__F2 b) /\ SRS_TPC_CommandConfig__F1 (SRS_TPC_CommandConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_TPC_CommandConfig__cond, SRS_TPC_CommandConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_TPC_CommandConfig__Format : T_Format SRS_TPC_CommandConfig__Type SRS_TPC_CommandConfig__cond :=
 proj2_format SRS_TPC_CommandConfig__cond SRS_TPC_CommandConfig__list_format  SRS_TPC_CommandConfig__F1 SRS_TPC_CommandConfig__F2 SRS_TPC_CommandConfig__helper1 SRS_TPC_CommandConfig__helper2 SRS_TPC_CommandConfig__helper3.

Opaque SRS_TPC_CommandConfig__cond SRS_TPC_CommandConfig__Format.

