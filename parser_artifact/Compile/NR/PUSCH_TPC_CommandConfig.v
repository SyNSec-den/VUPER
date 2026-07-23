Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUSCH_TPC_CommandConfig__tpc_Index__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma PUSCH_TPC_CommandConfig__tpc_Index__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_TPC_CommandConfig__tpc_Index__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_TPC_CommandConfig__tpc_Index__Type := Z.
Definition PUSCH_TPC_CommandConfig__tpc_Index__cond := (fun z => (1 <= z <= 15)%Z).
Lemma PUSCH_TPC_CommandConfig__tpc_IndexSUL__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma PUSCH_TPC_CommandConfig__tpc_IndexSUL__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_TPC_CommandConfig__tpc_IndexSUL__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_TPC_CommandConfig__tpc_IndexSUL__Type := Z.
Definition PUSCH_TPC_CommandConfig__tpc_IndexSUL__cond := (fun z => (1 <= z <= 15)%Z).
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Record PUSCH_TPC_CommandConfig__Type : Set :=
  make__PUSCH_TPC_CommandConfig__Type {
    PUSCH_TPC_CommandConfig__tpc_Index : option Z ;
    PUSCH_TPC_CommandConfig__tpc_IndexSUL : option Z ;
    PUSCH_TPC_CommandConfig__targetCell : option ServCellIndex__Type ;
}.
Definition PUSCH_TPC_CommandConfig__root_list : list seq_elem := (
 Opt Z PUSCH_TPC_CommandConfig__tpc_Index__cond ::
 Opt Z PUSCH_TPC_CommandConfig__tpc_IndexSUL__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 nil).
Definition PUSCH_TPC_CommandConfig__ext_list : list typ := (
  nil).
Definition PUSCH_TPC_CommandConfig__cond (z : PUSCH_TPC_CommandConfig__Type) := 
(  opt_cond PUSCH_TPC_CommandConfig__tpc_Index__cond (PUSCH_TPC_CommandConfig__tpc_Index z) /\
  opt_cond PUSCH_TPC_CommandConfig__tpc_IndexSUL__cond (PUSCH_TPC_CommandConfig__tpc_IndexSUL z) /\
  opt_cond ServCellIndex__cond (PUSCH_TPC_CommandConfig__targetCell z) /\
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
Definition PUSCH_TPC_CommandConfig__tpc_Index__Format : T_Format Z PUSCH_TPC_CommandConfig__tpc_Index__cond :=
 ranged_int_format (1) (15) PUSCH_TPC_CommandConfig__tpc_Index__helper1 PUSCH_TPC_CommandConfig__tpc_Index__helper2.

Opaque PUSCH_TPC_CommandConfig__tpc_Index__cond PUSCH_TPC_CommandConfig__tpc_Index__Format.

Definition PUSCH_TPC_CommandConfig__tpc_IndexSUL__Format : T_Format Z PUSCH_TPC_CommandConfig__tpc_IndexSUL__cond :=
 ranged_int_format (1) (15) PUSCH_TPC_CommandConfig__tpc_IndexSUL__helper1 PUSCH_TPC_CommandConfig__tpc_IndexSUL__helper2.

Opaque PUSCH_TPC_CommandConfig__tpc_IndexSUL__cond PUSCH_TPC_CommandConfig__tpc_IndexSUL__Format.


Definition PUSCH_TPC_CommandConfig__root_Format_Type := Eval cbn in seq_format_prod PUSCH_TPC_CommandConfig__root_list.
Definition PUSCH_TPC_CommandConfig__root_Format_list : PUSCH_TPC_CommandConfig__root_Format_Type :=
  (PUSCH_TPC_CommandConfig__tpc_Index__Format, (PUSCH_TPC_CommandConfig__tpc_IndexSUL__Format, (ServCellIndex__Format, unit_format))).

Definition PUSCH_TPC_CommandConfig__ext_Format_Type := Eval cbn in get_formats PUSCH_TPC_CommandConfig__ext_list.
Definition PUSCH_TPC_CommandConfig__ext_Format_list : PUSCH_TPC_CommandConfig__ext_Format_Type :=
  unit__Format.

Definition PUSCH_TPC_CommandConfig__list_type : Set := (seq_type PUSCH_TPC_CommandConfig__root_list) * (seq_ext_type PUSCH_TPC_CommandConfig__ext_list).
Definition PUSCH_TPC_CommandConfig__list_cond (z : PUSCH_TPC_CommandConfig__list_type) : Prop :=
        (seq_cond PUSCH_TPC_CommandConfig__root_list (fst z)) /\ (seq_ext_cond PUSCH_TPC_CommandConfig__ext_list (snd z)).
Definition PUSCH_TPC_CommandConfig__list_format : T_Format PUSCH_TPC_CommandConfig__list_type PUSCH_TPC_CommandConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PUSCH_TPC_CommandConfig__root_list PUSCH_TPC_CommandConfig__root_Format_list PUSCH_TPC_CommandConfig__ext_list PUSCH_TPC_CommandConfig__ext_Format_list.

Opaque PUSCH_TPC_CommandConfig__list_format.
Definition PUSCH_TPC_CommandConfig__F1 (z : PUSCH_TPC_CommandConfig__Type) : PUSCH_TPC_CommandConfig__list_type :=
  (((PUSCH_TPC_CommandConfig__tpc_Index z, (PUSCH_TPC_CommandConfig__tpc_IndexSUL z, (PUSCH_TPC_CommandConfig__targetCell z, tt)))), (
tt)).
Definition PUSCH_TPC_CommandConfig__F2 (y : PUSCH_TPC_CommandConfig__list_type) : PUSCH_TPC_CommandConfig__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__PUSCH_TPC_CommandConfig__Type j0 j1 j2
  end.
Definition PUSCH_TPC_CommandConfig__helper1 : (forall a : PUSCH_TPC_CommandConfig__Type, PUSCH_TPC_CommandConfig__cond a -> PUSCH_TPC_CommandConfig__list_cond (PUSCH_TPC_CommandConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUSCH_TPC_CommandConfig__helper2 : (forall a : PUSCH_TPC_CommandConfig__Type, PUSCH_TPC_CommandConfig__F2 (PUSCH_TPC_CommandConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUSCH_TPC_CommandConfig__helper3 : (forall b : PUSCH_TPC_CommandConfig__list_type, PUSCH_TPC_CommandConfig__list_cond b -> PUSCH_TPC_CommandConfig__cond (PUSCH_TPC_CommandConfig__F2 b) /\ PUSCH_TPC_CommandConfig__F1 (PUSCH_TPC_CommandConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUSCH_TPC_CommandConfig__cond, PUSCH_TPC_CommandConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUSCH_TPC_CommandConfig__Format : T_Format PUSCH_TPC_CommandConfig__Type PUSCH_TPC_CommandConfig__cond :=
 proj2_format PUSCH_TPC_CommandConfig__cond PUSCH_TPC_CommandConfig__list_format  PUSCH_TPC_CommandConfig__F1 PUSCH_TPC_CommandConfig__F2 PUSCH_TPC_CommandConfig__helper1 PUSCH_TPC_CommandConfig__helper2 PUSCH_TPC_CommandConfig__helper3.

Opaque PUSCH_TPC_CommandConfig__cond PUSCH_TPC_CommandConfig__Format.

