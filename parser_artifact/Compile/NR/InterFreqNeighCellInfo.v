Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma InterFreqNeighCellInfo__q_RxLevMinOffsetCell__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma InterFreqNeighCellInfo__q_RxLevMinOffsetCell__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply InterFreqNeighCellInfo__q_RxLevMinOffsetCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition InterFreqNeighCellInfo__q_RxLevMinOffsetCell__Type := Z.
Definition InterFreqNeighCellInfo__q_RxLevMinOffsetCell__cond := (fun z => (1 <= z <= 8)%Z).
Lemma InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__Type := Z.
Definition InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond := (fun z => (1 <= z <= 8)%Z).
Lemma InterFreqNeighCellInfo__q_QualMinOffsetCell__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma InterFreqNeighCellInfo__q_QualMinOffsetCell__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply InterFreqNeighCellInfo__q_QualMinOffsetCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition InterFreqNeighCellInfo__q_QualMinOffsetCell__Type := Z.
Definition InterFreqNeighCellInfo__q_QualMinOffsetCell__cond := (fun z => (1 <= z <= 8)%Z).
Record InterFreqNeighCellInfo__Type : Set :=
  make__InterFreqNeighCellInfo__Type {
    InterFreqNeighCellInfo__physCellId : PhysCellId__Type ;
    InterFreqNeighCellInfo__q_OffsetCell : Q_OffsetRange__Type ;
    InterFreqNeighCellInfo__q_RxLevMinOffsetCell : option Z ;
    InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL : option Z ;
    InterFreqNeighCellInfo__q_QualMinOffsetCell : option Z ;
}.
Definition InterFreqNeighCellInfo__root_list : list seq_elem := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor Q_OffsetRange__Type Q_OffsetRange__cond ::
 Opt Z InterFreqNeighCellInfo__q_RxLevMinOffsetCell__cond ::
 Opt Z InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond ::
 Opt Z InterFreqNeighCellInfo__q_QualMinOffsetCell__cond ::
 nil).
Definition InterFreqNeighCellInfo__ext_list : list typ := (
  nil).
Definition InterFreqNeighCellInfo__cond (z : InterFreqNeighCellInfo__Type) := 
(  PhysCellId__cond (InterFreqNeighCellInfo__physCellId z) /\
  Q_OffsetRange__cond (InterFreqNeighCellInfo__q_OffsetCell z) /\
  opt_cond InterFreqNeighCellInfo__q_RxLevMinOffsetCell__cond (InterFreqNeighCellInfo__q_RxLevMinOffsetCell z) /\
  opt_cond InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond (InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL z) /\
  opt_cond InterFreqNeighCellInfo__q_QualMinOffsetCell__cond (InterFreqNeighCellInfo__q_QualMinOffsetCell z) /\
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
Definition InterFreqNeighCellInfo__q_RxLevMinOffsetCell__Format : T_Format Z InterFreqNeighCellInfo__q_RxLevMinOffsetCell__cond :=
 ranged_int_format (1) (8) InterFreqNeighCellInfo__q_RxLevMinOffsetCell__helper1 InterFreqNeighCellInfo__q_RxLevMinOffsetCell__helper2.

Opaque InterFreqNeighCellInfo__q_RxLevMinOffsetCell__cond InterFreqNeighCellInfo__q_RxLevMinOffsetCell__Format.

Definition InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__Format : T_Format Z InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond :=
 ranged_int_format (1) (8) InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper1 InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper2.

Opaque InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__Format.

Definition InterFreqNeighCellInfo__q_QualMinOffsetCell__Format : T_Format Z InterFreqNeighCellInfo__q_QualMinOffsetCell__cond :=
 ranged_int_format (1) (8) InterFreqNeighCellInfo__q_QualMinOffsetCell__helper1 InterFreqNeighCellInfo__q_QualMinOffsetCell__helper2.

Opaque InterFreqNeighCellInfo__q_QualMinOffsetCell__cond InterFreqNeighCellInfo__q_QualMinOffsetCell__Format.


Definition InterFreqNeighCellInfo__root_Format_Type := Eval cbn in seq_format_prod InterFreqNeighCellInfo__root_list.
Definition InterFreqNeighCellInfo__root_Format_list : InterFreqNeighCellInfo__root_Format_Type :=
  (PhysCellId__Format, (Q_OffsetRange__Format, (InterFreqNeighCellInfo__q_RxLevMinOffsetCell__Format, (InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__Format, (InterFreqNeighCellInfo__q_QualMinOffsetCell__Format, unit_format))))).

Definition InterFreqNeighCellInfo__ext_Format_Type := Eval cbn in get_formats InterFreqNeighCellInfo__ext_list.
Definition InterFreqNeighCellInfo__ext_Format_list : InterFreqNeighCellInfo__ext_Format_Type :=
  unit__Format.

Definition InterFreqNeighCellInfo__list_type : Set := (seq_type InterFreqNeighCellInfo__root_list) * (seq_ext_type InterFreqNeighCellInfo__ext_list).
Definition InterFreqNeighCellInfo__list_cond (z : InterFreqNeighCellInfo__list_type) : Prop :=
        (seq_cond InterFreqNeighCellInfo__root_list (fst z)) /\ (seq_ext_cond InterFreqNeighCellInfo__ext_list (snd z)).
Definition InterFreqNeighCellInfo__list_format : T_Format InterFreqNeighCellInfo__list_type InterFreqNeighCellInfo__list_cond :=
 (* Eval compute in *) seq_ext_format InterFreqNeighCellInfo__root_list InterFreqNeighCellInfo__root_Format_list InterFreqNeighCellInfo__ext_list InterFreqNeighCellInfo__ext_Format_list.

Opaque InterFreqNeighCellInfo__list_format.
Definition InterFreqNeighCellInfo__F1 (z : InterFreqNeighCellInfo__Type) : InterFreqNeighCellInfo__list_type :=
  (((InterFreqNeighCellInfo__physCellId z, (InterFreqNeighCellInfo__q_OffsetCell z, (InterFreqNeighCellInfo__q_RxLevMinOffsetCell z, (InterFreqNeighCellInfo__q_RxLevMinOffsetCellSUL z, (InterFreqNeighCellInfo__q_QualMinOffsetCell z, tt)))))), (
tt)).
Definition InterFreqNeighCellInfo__F2 (y : InterFreqNeighCellInfo__list_type) : InterFreqNeighCellInfo__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__InterFreqNeighCellInfo__Type j0 j1 j2 j3 j4
  end.
Definition InterFreqNeighCellInfo__helper1 : (forall a : InterFreqNeighCellInfo__Type, InterFreqNeighCellInfo__cond a -> InterFreqNeighCellInfo__list_cond (InterFreqNeighCellInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition InterFreqNeighCellInfo__helper2 : (forall a : InterFreqNeighCellInfo__Type, InterFreqNeighCellInfo__F2 (InterFreqNeighCellInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition InterFreqNeighCellInfo__helper3 : (forall b : InterFreqNeighCellInfo__list_type, InterFreqNeighCellInfo__list_cond b -> InterFreqNeighCellInfo__cond (InterFreqNeighCellInfo__F2 b) /\ InterFreqNeighCellInfo__F1 (InterFreqNeighCellInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold InterFreqNeighCellInfo__cond, InterFreqNeighCellInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition InterFreqNeighCellInfo__Format : T_Format InterFreqNeighCellInfo__Type InterFreqNeighCellInfo__cond :=
 proj2_format InterFreqNeighCellInfo__cond InterFreqNeighCellInfo__list_format  InterFreqNeighCellInfo__F1 InterFreqNeighCellInfo__F2 InterFreqNeighCellInfo__helper1 InterFreqNeighCellInfo__helper2 InterFreqNeighCellInfo__helper3.

Opaque InterFreqNeighCellInfo__cond InterFreqNeighCellInfo__Format.

