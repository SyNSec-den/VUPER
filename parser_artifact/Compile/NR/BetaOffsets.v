Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma BetaOffsets__betaOffsetACK_Index1__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma BetaOffsets__betaOffsetACK_Index1__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BetaOffsets__betaOffsetACK_Index1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BetaOffsets__betaOffsetACK_Index1__Type := Z.
Definition BetaOffsets__betaOffsetACK_Index1__cond := (fun z => (0 <= z <= 31)%Z).
Lemma BetaOffsets__betaOffsetACK_Index2__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma BetaOffsets__betaOffsetACK_Index2__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BetaOffsets__betaOffsetACK_Index2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BetaOffsets__betaOffsetACK_Index2__Type := Z.
Definition BetaOffsets__betaOffsetACK_Index2__cond := (fun z => (0 <= z <= 31)%Z).
Lemma BetaOffsets__betaOffsetACK_Index3__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma BetaOffsets__betaOffsetACK_Index3__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BetaOffsets__betaOffsetACK_Index3__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BetaOffsets__betaOffsetACK_Index3__Type := Z.
Definition BetaOffsets__betaOffsetACK_Index3__cond := (fun z => (0 <= z <= 31)%Z).
Lemma BetaOffsets__betaOffsetCSI_Part1_Index1__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma BetaOffsets__betaOffsetCSI_Part1_Index1__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BetaOffsets__betaOffsetCSI_Part1_Index1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BetaOffsets__betaOffsetCSI_Part1_Index1__Type := Z.
Definition BetaOffsets__betaOffsetCSI_Part1_Index1__cond := (fun z => (0 <= z <= 31)%Z).
Lemma BetaOffsets__betaOffsetCSI_Part1_Index2__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma BetaOffsets__betaOffsetCSI_Part1_Index2__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BetaOffsets__betaOffsetCSI_Part1_Index2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BetaOffsets__betaOffsetCSI_Part1_Index2__Type := Z.
Definition BetaOffsets__betaOffsetCSI_Part1_Index2__cond := (fun z => (0 <= z <= 31)%Z).
Lemma BetaOffsets__betaOffsetCSI_Part2_Index1__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma BetaOffsets__betaOffsetCSI_Part2_Index1__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BetaOffsets__betaOffsetCSI_Part2_Index1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BetaOffsets__betaOffsetCSI_Part2_Index1__Type := Z.
Definition BetaOffsets__betaOffsetCSI_Part2_Index1__cond := (fun z => (0 <= z <= 31)%Z).
Lemma BetaOffsets__betaOffsetCSI_Part2_Index2__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma BetaOffsets__betaOffsetCSI_Part2_Index2__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BetaOffsets__betaOffsetCSI_Part2_Index2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BetaOffsets__betaOffsetCSI_Part2_Index2__Type := Z.
Definition BetaOffsets__betaOffsetCSI_Part2_Index2__cond := (fun z => (0 <= z <= 31)%Z).
Record BetaOffsets__Type : Set :=
  make__BetaOffsets__Type {
    BetaOffsets__betaOffsetACK_Index1 : option Z ;
    BetaOffsets__betaOffsetACK_Index2 : option Z ;
    BetaOffsets__betaOffsetACK_Index3 : option Z ;
    BetaOffsets__betaOffsetCSI_Part1_Index1 : option Z ;
    BetaOffsets__betaOffsetCSI_Part1_Index2 : option Z ;
    BetaOffsets__betaOffsetCSI_Part2_Index1 : option Z ;
    BetaOffsets__betaOffsetCSI_Part2_Index2 : option Z ;
}.
Definition BetaOffsets__list := (
 Opt Z BetaOffsets__betaOffsetACK_Index1__cond ::
 Opt Z BetaOffsets__betaOffsetACK_Index2__cond ::
 Opt Z BetaOffsets__betaOffsetACK_Index3__cond ::
 Opt Z BetaOffsets__betaOffsetCSI_Part1_Index1__cond ::
 Opt Z BetaOffsets__betaOffsetCSI_Part1_Index2__cond ::
 Opt Z BetaOffsets__betaOffsetCSI_Part2_Index1__cond ::
 Opt Z BetaOffsets__betaOffsetCSI_Part2_Index2__cond ::
 nil).
Definition BetaOffsets__cond z := 
  opt_cond BetaOffsets__betaOffsetACK_Index1__cond (BetaOffsets__betaOffsetACK_Index1 z) /\
  opt_cond BetaOffsets__betaOffsetACK_Index2__cond (BetaOffsets__betaOffsetACK_Index2 z) /\
  opt_cond BetaOffsets__betaOffsetACK_Index3__cond (BetaOffsets__betaOffsetACK_Index3 z) /\
  opt_cond BetaOffsets__betaOffsetCSI_Part1_Index1__cond (BetaOffsets__betaOffsetCSI_Part1_Index1 z) /\
  opt_cond BetaOffsets__betaOffsetCSI_Part1_Index2__cond (BetaOffsets__betaOffsetCSI_Part1_Index2 z) /\
  opt_cond BetaOffsets__betaOffsetCSI_Part2_Index1__cond (BetaOffsets__betaOffsetCSI_Part2_Index1 z) /\
  opt_cond BetaOffsets__betaOffsetCSI_Part2_Index2__cond (BetaOffsets__betaOffsetCSI_Part2_Index2 z) /\
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
Definition BetaOffsets__betaOffsetACK_Index1__Format : T_Format Z BetaOffsets__betaOffsetACK_Index1__cond :=
 ranged_int_format (0) (31) BetaOffsets__betaOffsetACK_Index1__helper1 BetaOffsets__betaOffsetACK_Index1__helper2.

Opaque BetaOffsets__betaOffsetACK_Index1__cond BetaOffsets__betaOffsetACK_Index1__Format.

Definition BetaOffsets__betaOffsetACK_Index2__Format : T_Format Z BetaOffsets__betaOffsetACK_Index2__cond :=
 ranged_int_format (0) (31) BetaOffsets__betaOffsetACK_Index2__helper1 BetaOffsets__betaOffsetACK_Index2__helper2.

Opaque BetaOffsets__betaOffsetACK_Index2__cond BetaOffsets__betaOffsetACK_Index2__Format.

Definition BetaOffsets__betaOffsetACK_Index3__Format : T_Format Z BetaOffsets__betaOffsetACK_Index3__cond :=
 ranged_int_format (0) (31) BetaOffsets__betaOffsetACK_Index3__helper1 BetaOffsets__betaOffsetACK_Index3__helper2.

Opaque BetaOffsets__betaOffsetACK_Index3__cond BetaOffsets__betaOffsetACK_Index3__Format.

Definition BetaOffsets__betaOffsetCSI_Part1_Index1__Format : T_Format Z BetaOffsets__betaOffsetCSI_Part1_Index1__cond :=
 ranged_int_format (0) (31) BetaOffsets__betaOffsetCSI_Part1_Index1__helper1 BetaOffsets__betaOffsetCSI_Part1_Index1__helper2.

Opaque BetaOffsets__betaOffsetCSI_Part1_Index1__cond BetaOffsets__betaOffsetCSI_Part1_Index1__Format.

Definition BetaOffsets__betaOffsetCSI_Part1_Index2__Format : T_Format Z BetaOffsets__betaOffsetCSI_Part1_Index2__cond :=
 ranged_int_format (0) (31) BetaOffsets__betaOffsetCSI_Part1_Index2__helper1 BetaOffsets__betaOffsetCSI_Part1_Index2__helper2.

Opaque BetaOffsets__betaOffsetCSI_Part1_Index2__cond BetaOffsets__betaOffsetCSI_Part1_Index2__Format.

Definition BetaOffsets__betaOffsetCSI_Part2_Index1__Format : T_Format Z BetaOffsets__betaOffsetCSI_Part2_Index1__cond :=
 ranged_int_format (0) (31) BetaOffsets__betaOffsetCSI_Part2_Index1__helper1 BetaOffsets__betaOffsetCSI_Part2_Index1__helper2.

Opaque BetaOffsets__betaOffsetCSI_Part2_Index1__cond BetaOffsets__betaOffsetCSI_Part2_Index1__Format.

Definition BetaOffsets__betaOffsetCSI_Part2_Index2__Format : T_Format Z BetaOffsets__betaOffsetCSI_Part2_Index2__cond :=
 ranged_int_format (0) (31) BetaOffsets__betaOffsetCSI_Part2_Index2__helper1 BetaOffsets__betaOffsetCSI_Part2_Index2__helper2.

Opaque BetaOffsets__betaOffsetCSI_Part2_Index2__cond BetaOffsets__betaOffsetCSI_Part2_Index2__Format.


Definition BetaOffsets__Format_Type := Eval cbn in seq_format_prod BetaOffsets__list.
Definition BetaOffsets__Format_list : BetaOffsets__Format_Type :=
  (BetaOffsets__betaOffsetACK_Index1__Format, (BetaOffsets__betaOffsetACK_Index2__Format, (BetaOffsets__betaOffsetACK_Index3__Format, (BetaOffsets__betaOffsetCSI_Part1_Index1__Format, (BetaOffsets__betaOffsetCSI_Part1_Index2__Format, (BetaOffsets__betaOffsetCSI_Part2_Index1__Format, (BetaOffsets__betaOffsetCSI_Part2_Index2__Format, unit_format))))))).
Definition BetaOffsets__list__Format := (*Eval compute in *) seq_format BetaOffsets__list BetaOffsets__Format_list.
Definition BetaOffsets__F1 z :=
  (BetaOffsets__betaOffsetACK_Index1 z, (BetaOffsets__betaOffsetACK_Index2 z, (BetaOffsets__betaOffsetACK_Index3 z, (BetaOffsets__betaOffsetCSI_Part1_Index1 z, (BetaOffsets__betaOffsetCSI_Part1_Index2 z, (BetaOffsets__betaOffsetCSI_Part2_Index1 z, (BetaOffsets__betaOffsetCSI_Part2_Index2 z, tt))))))).
Definition BetaOffsets__F2 (y : seq_type BetaOffsets__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__BetaOffsets__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma BetaOffsets__F1F2_cond (z : BetaOffsets__Type)
  : BetaOffsets__cond z ->
  (seq_cond BetaOffsets__list (BetaOffsets__F1 z)).
intro H. unfold BetaOffsets__cond in H. simpl. auto. Qed.
Lemma BetaOffsets__F1F2_cond2 (z : BetaOffsets__Type)
 : BetaOffsets__F2 (BetaOffsets__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BetaOffsets__F2F1_cond (y : seq_type BetaOffsets__list)
  : seq_cond BetaOffsets__list y ->
 (BetaOffsets__cond (BetaOffsets__F2 y)) /\  BetaOffsets__F1 (BetaOffsets__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BetaOffsets__cond. simpl in *. auto.
 - simpl. unfold BetaOffsets__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BetaOffsets__Format : T_Format BetaOffsets__Type BetaOffsets__cond :=
        proj2_format  BetaOffsets__cond BetaOffsets__list__Format
    BetaOffsets__F1 BetaOffsets__F2 BetaOffsets__F1F2_cond  BetaOffsets__F1F2_cond2 BetaOffsets__F2F1_cond.
Opaque BetaOffsets__cond BetaOffsets__Format.

