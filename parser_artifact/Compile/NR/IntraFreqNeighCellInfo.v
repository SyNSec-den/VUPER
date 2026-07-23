Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.Q_OffsetRange.

Opaque Q_OffsetRange__cond Q_OffsetRange__Format.

Lemma IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__Type := Z.
Definition IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__cond := (fun z => (1 <= z <= 8)%Z).
Lemma IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__Type := Z.
Definition IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond := (fun z => (1 <= z <= 8)%Z).
Lemma IntraFreqNeighCellInfo__q_QualMinOffsetCell__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma IntraFreqNeighCellInfo__q_QualMinOffsetCell__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IntraFreqNeighCellInfo__q_QualMinOffsetCell__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IntraFreqNeighCellInfo__q_QualMinOffsetCell__Type := Z.
Definition IntraFreqNeighCellInfo__q_QualMinOffsetCell__cond := (fun z => (1 <= z <= 8)%Z).
Record IntraFreqNeighCellInfo__Type : Set :=
  make__IntraFreqNeighCellInfo__Type {
    IntraFreqNeighCellInfo__physCellId : PhysCellId__Type ;
    IntraFreqNeighCellInfo__q_OffsetCell : Q_OffsetRange__Type ;
    IntraFreqNeighCellInfo__q_RxLevMinOffsetCell : option Z ;
    IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL : option Z ;
    IntraFreqNeighCellInfo__q_QualMinOffsetCell : option Z ;
}.
Definition IntraFreqNeighCellInfo__root_list : list seq_elem := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor Q_OffsetRange__Type Q_OffsetRange__cond ::
 Opt Z IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__cond ::
 Opt Z IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond ::
 Opt Z IntraFreqNeighCellInfo__q_QualMinOffsetCell__cond ::
 nil).
Definition IntraFreqNeighCellInfo__ext_list : list typ := (
  nil).
Definition IntraFreqNeighCellInfo__cond (z : IntraFreqNeighCellInfo__Type) := 
(  PhysCellId__cond (IntraFreqNeighCellInfo__physCellId z) /\
  Q_OffsetRange__cond (IntraFreqNeighCellInfo__q_OffsetCell z) /\
  opt_cond IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__cond (IntraFreqNeighCellInfo__q_RxLevMinOffsetCell z) /\
  opt_cond IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond (IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL z) /\
  opt_cond IntraFreqNeighCellInfo__q_QualMinOffsetCell__cond (IntraFreqNeighCellInfo__q_QualMinOffsetCell z) /\
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
Definition IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__Format : T_Format Z IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__cond :=
 ranged_int_format (1) (8) IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__helper1 IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__helper2.

Opaque IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__cond IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__Format.

Definition IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__Format : T_Format Z IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond :=
 ranged_int_format (1) (8) IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper1 IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__helper2.

Opaque IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__cond IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__Format.

Definition IntraFreqNeighCellInfo__q_QualMinOffsetCell__Format : T_Format Z IntraFreqNeighCellInfo__q_QualMinOffsetCell__cond :=
 ranged_int_format (1) (8) IntraFreqNeighCellInfo__q_QualMinOffsetCell__helper1 IntraFreqNeighCellInfo__q_QualMinOffsetCell__helper2.

Opaque IntraFreqNeighCellInfo__q_QualMinOffsetCell__cond IntraFreqNeighCellInfo__q_QualMinOffsetCell__Format.


Definition IntraFreqNeighCellInfo__root_Format_Type := Eval cbn in seq_format_prod IntraFreqNeighCellInfo__root_list.
Definition IntraFreqNeighCellInfo__root_Format_list : IntraFreqNeighCellInfo__root_Format_Type :=
  (PhysCellId__Format, (Q_OffsetRange__Format, (IntraFreqNeighCellInfo__q_RxLevMinOffsetCell__Format, (IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL__Format, (IntraFreqNeighCellInfo__q_QualMinOffsetCell__Format, unit_format))))).

Definition IntraFreqNeighCellInfo__ext_Format_Type := Eval cbn in get_formats IntraFreqNeighCellInfo__ext_list.
Definition IntraFreqNeighCellInfo__ext_Format_list : IntraFreqNeighCellInfo__ext_Format_Type :=
  unit__Format.

Definition IntraFreqNeighCellInfo__list_type : Set := (seq_type IntraFreqNeighCellInfo__root_list) * (seq_ext_type IntraFreqNeighCellInfo__ext_list).
Definition IntraFreqNeighCellInfo__list_cond (z : IntraFreqNeighCellInfo__list_type) : Prop :=
        (seq_cond IntraFreqNeighCellInfo__root_list (fst z)) /\ (seq_ext_cond IntraFreqNeighCellInfo__ext_list (snd z)).
Definition IntraFreqNeighCellInfo__list_format : T_Format IntraFreqNeighCellInfo__list_type IntraFreqNeighCellInfo__list_cond :=
 (* Eval compute in *) seq_ext_format IntraFreqNeighCellInfo__root_list IntraFreqNeighCellInfo__root_Format_list IntraFreqNeighCellInfo__ext_list IntraFreqNeighCellInfo__ext_Format_list.

Opaque IntraFreqNeighCellInfo__list_format.
Definition IntraFreqNeighCellInfo__F1 (z : IntraFreqNeighCellInfo__Type) : IntraFreqNeighCellInfo__list_type :=
  (((IntraFreqNeighCellInfo__physCellId z, (IntraFreqNeighCellInfo__q_OffsetCell z, (IntraFreqNeighCellInfo__q_RxLevMinOffsetCell z, (IntraFreqNeighCellInfo__q_RxLevMinOffsetCellSUL z, (IntraFreqNeighCellInfo__q_QualMinOffsetCell z, tt)))))), (
tt)).
Definition IntraFreqNeighCellInfo__F2 (y : IntraFreqNeighCellInfo__list_type) : IntraFreqNeighCellInfo__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__IntraFreqNeighCellInfo__Type j0 j1 j2 j3 j4
  end.
Definition IntraFreqNeighCellInfo__helper1 : (forall a : IntraFreqNeighCellInfo__Type, IntraFreqNeighCellInfo__cond a -> IntraFreqNeighCellInfo__list_cond (IntraFreqNeighCellInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition IntraFreqNeighCellInfo__helper2 : (forall a : IntraFreqNeighCellInfo__Type, IntraFreqNeighCellInfo__F2 (IntraFreqNeighCellInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition IntraFreqNeighCellInfo__helper3 : (forall b : IntraFreqNeighCellInfo__list_type, IntraFreqNeighCellInfo__list_cond b -> IntraFreqNeighCellInfo__cond (IntraFreqNeighCellInfo__F2 b) /\ IntraFreqNeighCellInfo__F1 (IntraFreqNeighCellInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold IntraFreqNeighCellInfo__cond, IntraFreqNeighCellInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition IntraFreqNeighCellInfo__Format : T_Format IntraFreqNeighCellInfo__Type IntraFreqNeighCellInfo__cond :=
 proj2_format IntraFreqNeighCellInfo__cond IntraFreqNeighCellInfo__list_format  IntraFreqNeighCellInfo__F1 IntraFreqNeighCellInfo__F2 IntraFreqNeighCellInfo__helper1 IntraFreqNeighCellInfo__helper2 IntraFreqNeighCellInfo__helper3.

Opaque IntraFreqNeighCellInfo__cond IntraFreqNeighCellInfo__Format.

