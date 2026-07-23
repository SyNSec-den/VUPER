Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellIdUTRA_FDD_r16.

Opaque PhysCellIdUTRA_FDD_r16__cond PhysCellIdUTRA_FDD_r16__Format.

Lemma MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__helper1 : (-5 <= 91)%Z.  lia. Qed.
Lemma MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__helper2 : to_bit_sz (Z.to_nat (91 - -5)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (91 - -5))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__Type := Z.
Definition MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__cond := (fun z => (-5 <= z <= 91)%Z).
Lemma MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__helper1 : (0 <= 49)%Z.  lia. Qed.
Lemma MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__helper2 : to_bit_sz (Z.to_nat (49 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (49 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__Type := Z.
Definition MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__cond := (fun z => (0 <= z <= 49)%Z).
Record MeasResultUTRA_FDD_r16__measResult_r16__Type : Set :=
  make__MeasResultUTRA_FDD_r16__measResult_r16__Type {
    MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16 : option Z ;
    MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16 : option Z ;
}.
Definition MeasResultUTRA_FDD_r16__measResult_r16__list := (
 Opt Z MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__cond ::
 Opt Z MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__cond ::
 nil).
Definition MeasResultUTRA_FDD_r16__measResult_r16__cond z := 
  opt_cond MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__cond (MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16 z) /\
  opt_cond MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__cond (MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16 z) /\
  True.

Record MeasResultUTRA_FDD_r16__Type : Set :=
  make__MeasResultUTRA_FDD_r16__Type {
    MeasResultUTRA_FDD_r16__physCellId_r16 : PhysCellIdUTRA_FDD_r16__Type ;
    MeasResultUTRA_FDD_r16__measResult_r16 : MeasResultUTRA_FDD_r16__measResult_r16__Type ;
}.
Definition MeasResultUTRA_FDD_r16__list := (
 Nor PhysCellIdUTRA_FDD_r16__Type PhysCellIdUTRA_FDD_r16__cond ::
 Nor MeasResultUTRA_FDD_r16__measResult_r16__Type MeasResultUTRA_FDD_r16__measResult_r16__cond ::
 nil).
Definition MeasResultUTRA_FDD_r16__cond z := 
  PhysCellIdUTRA_FDD_r16__cond (MeasResultUTRA_FDD_r16__physCellId_r16 z) /\
  MeasResultUTRA_FDD_r16__measResult_r16__cond (MeasResultUTRA_FDD_r16__measResult_r16 z) /\
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
Definition MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__Format : T_Format Z MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__cond :=
 ranged_int_format (-5) (91) MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__helper1 MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__helper2.

Opaque MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__cond MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__Format.

Definition MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__Format : T_Format Z MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__cond :=
 ranged_int_format (0) (49) MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__helper1 MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__helper2.

Opaque MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__cond MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__Format.


Definition MeasResultUTRA_FDD_r16__measResult_r16__Format_Type := Eval cbn in seq_format_prod MeasResultUTRA_FDD_r16__measResult_r16__list.
Definition MeasResultUTRA_FDD_r16__measResult_r16__Format_list : MeasResultUTRA_FDD_r16__measResult_r16__Format_Type :=
  (MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16__Format, (MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16__Format, unit_format)).
Definition MeasResultUTRA_FDD_r16__measResult_r16__list__Format := (*Eval compute in *) seq_format MeasResultUTRA_FDD_r16__measResult_r16__list MeasResultUTRA_FDD_r16__measResult_r16__Format_list.
Definition MeasResultUTRA_FDD_r16__measResult_r16__F1 z :=
  (MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_RSCP_r16 z, (MeasResultUTRA_FDD_r16__measResult_r16__utra_FDD_EcN0_r16 z, tt)).
Definition MeasResultUTRA_FDD_r16__measResult_r16__F2 (y : seq_type MeasResultUTRA_FDD_r16__measResult_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultUTRA_FDD_r16__measResult_r16__Type i0 i1
  end.
Lemma MeasResultUTRA_FDD_r16__measResult_r16__F1F2_cond (z : MeasResultUTRA_FDD_r16__measResult_r16__Type)
  : MeasResultUTRA_FDD_r16__measResult_r16__cond z ->
  (seq_cond MeasResultUTRA_FDD_r16__measResult_r16__list (MeasResultUTRA_FDD_r16__measResult_r16__F1 z)).
intro H. unfold MeasResultUTRA_FDD_r16__measResult_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultUTRA_FDD_r16__measResult_r16__F1F2_cond2 (z : MeasResultUTRA_FDD_r16__measResult_r16__Type)
 : MeasResultUTRA_FDD_r16__measResult_r16__F2 (MeasResultUTRA_FDD_r16__measResult_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultUTRA_FDD_r16__measResult_r16__F2F1_cond (y : seq_type MeasResultUTRA_FDD_r16__measResult_r16__list)
  : seq_cond MeasResultUTRA_FDD_r16__measResult_r16__list y ->
 (MeasResultUTRA_FDD_r16__measResult_r16__cond (MeasResultUTRA_FDD_r16__measResult_r16__F2 y)) /\  MeasResultUTRA_FDD_r16__measResult_r16__F1 (MeasResultUTRA_FDD_r16__measResult_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultUTRA_FDD_r16__measResult_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultUTRA_FDD_r16__measResult_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultUTRA_FDD_r16__measResult_r16__Format : T_Format MeasResultUTRA_FDD_r16__measResult_r16__Type MeasResultUTRA_FDD_r16__measResult_r16__cond :=
        proj2_format  MeasResultUTRA_FDD_r16__measResult_r16__cond MeasResultUTRA_FDD_r16__measResult_r16__list__Format
    MeasResultUTRA_FDD_r16__measResult_r16__F1 MeasResultUTRA_FDD_r16__measResult_r16__F2 MeasResultUTRA_FDD_r16__measResult_r16__F1F2_cond  MeasResultUTRA_FDD_r16__measResult_r16__F1F2_cond2 MeasResultUTRA_FDD_r16__measResult_r16__F2F1_cond.
Opaque MeasResultUTRA_FDD_r16__measResult_r16__cond MeasResultUTRA_FDD_r16__measResult_r16__Format.


Definition MeasResultUTRA_FDD_r16__Format_Type := Eval cbn in seq_format_prod MeasResultUTRA_FDD_r16__list.
Definition MeasResultUTRA_FDD_r16__Format_list : MeasResultUTRA_FDD_r16__Format_Type :=
  (PhysCellIdUTRA_FDD_r16__Format, (MeasResultUTRA_FDD_r16__measResult_r16__Format, unit_format)).
Definition MeasResultUTRA_FDD_r16__list__Format := (*Eval compute in *) seq_format MeasResultUTRA_FDD_r16__list MeasResultUTRA_FDD_r16__Format_list.
Definition MeasResultUTRA_FDD_r16__F1 z :=
  (MeasResultUTRA_FDD_r16__physCellId_r16 z, (MeasResultUTRA_FDD_r16__measResult_r16 z, tt)).
Definition MeasResultUTRA_FDD_r16__F2 (y : seq_type MeasResultUTRA_FDD_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasResultUTRA_FDD_r16__Type i0 i1
  end.
Lemma MeasResultUTRA_FDD_r16__F1F2_cond (z : MeasResultUTRA_FDD_r16__Type)
  : MeasResultUTRA_FDD_r16__cond z ->
  (seq_cond MeasResultUTRA_FDD_r16__list (MeasResultUTRA_FDD_r16__F1 z)).
intro H. unfold MeasResultUTRA_FDD_r16__cond in H. simpl. auto. Qed.
Lemma MeasResultUTRA_FDD_r16__F1F2_cond2 (z : MeasResultUTRA_FDD_r16__Type)
 : MeasResultUTRA_FDD_r16__F2 (MeasResultUTRA_FDD_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasResultUTRA_FDD_r16__F2F1_cond (y : seq_type MeasResultUTRA_FDD_r16__list)
  : seq_cond MeasResultUTRA_FDD_r16__list y ->
 (MeasResultUTRA_FDD_r16__cond (MeasResultUTRA_FDD_r16__F2 y)) /\  MeasResultUTRA_FDD_r16__F1 (MeasResultUTRA_FDD_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasResultUTRA_FDD_r16__cond. simpl in *. auto.
 - simpl. unfold MeasResultUTRA_FDD_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasResultUTRA_FDD_r16__Format : T_Format MeasResultUTRA_FDD_r16__Type MeasResultUTRA_FDD_r16__cond :=
        proj2_format  MeasResultUTRA_FDD_r16__cond MeasResultUTRA_FDD_r16__list__Format
    MeasResultUTRA_FDD_r16__F1 MeasResultUTRA_FDD_r16__F2 MeasResultUTRA_FDD_r16__F1F2_cond  MeasResultUTRA_FDD_r16__F1F2_cond2 MeasResultUTRA_FDD_r16__F2F1_cond.
Opaque MeasResultUTRA_FDD_r16__cond MeasResultUTRA_FDD_r16__Format.

