Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NR_DL_PRS_ResourceID_r17.

Opaque NR_DL_PRS_ResourceID_r17__cond NR_DL_PRS_ResourceID_r17__Format.

Lemma NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__helper1 : (0 <= 4095)%Z.  lia. Qed.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__helper2 : to_bit_sz (Z.to_nat (4095 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4095 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__Type := Z.
Definition NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__cond := (fun z => (0 <= z <= 4095)%Z).
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__Type := Z.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__cond := (fun z => (0 <= z <= 1)%Z).
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__Type := Z.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__cond := (fun z => (0 <= z <= 3)%Z).
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__helper1 : (0 <= 5)%Z.  lia. Qed.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__helper2 : to_bit_sz (Z.to_nat (5 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__Type := Z.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__cond := (fun z => (0 <= z <= 5)%Z).
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__helper1 : (0 <= 11)%Z.  lia. Qed.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__helper2 : to_bit_sz (Z.to_nat (11 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (11 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__Type := Z.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__cond := (fun z => (0 <= z <= 11)%Z).

Inductive NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type : Set :=
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17 : Z -> NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17 : Z -> NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17 : Z -> NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17 : Z -> NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type
.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list : list typ := (
typ_cons Z NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__cond ::
typ_cons Z NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__cond ::
typ_cons Z NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__cond ::
typ_cons Z NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__cond ::
 nil).
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__cond (c : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type) := 
  match c with
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17 t => NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__cond t 
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17 t => NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__cond t 
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17 t => NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__cond t 
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17 t => NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__cond t 
  end.

Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__len_helper1 : to_bit_sz (length NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__len_helper2 : 2 <= length2 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list.
 simpl. lia. Qed.

Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__Type : Set := Empty_set.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__cond (c : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__Type) := True.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__Type : Set := NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type + NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__Type.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__cond :=
  sum_cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__cond.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__helper1 : (0 <= maxNrofPRS_ResourceOffsetValue_1_r17)%Z. unfold maxNrofPRS_ResourceOffsetValue_1_r17.
 lia. Qed.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPRS_ResourceOffsetValue_1_r17 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPRS_ResourceOffsetValue_1_r17 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__Type := Z.
Definition NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__cond := (fun z => (0 <= z <= maxNrofPRS_ResourceOffsetValue_1_r17)%Z).
Lemma NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__helper1 : (0 <= 12)%Z.  lia. Qed.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__helper2 : to_bit_sz (Z.to_nat (12 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (12 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__Type := Z.
Definition NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__cond := (fun z => (0 <= z <= 12)%Z).
Require Import NR.DL_PRS_QCL_Info_r17.

Opaque DL_PRS_QCL_Info_r17__cond DL_PRS_QCL_Info_r17__Format.

Record NR_DL_PRS_Resource_r17__Type : Set :=
  make__NR_DL_PRS_Resource_r17__Type {
    NR_DL_PRS_Resource_r17__nr_DL_PRS_ResourceID_r17 : NR_DL_PRS_ResourceID_r17__Type ;
    NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17 : Z ;
    NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17 : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__Type ;
    NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17 : Z ;
    NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17 : Z ;
    NR_DL_PRS_Resource_r17__dl_PRS_QCL_Info_r17 : option DL_PRS_QCL_Info_r17__Type ;
}.
Definition NR_DL_PRS_Resource_r17__root_list : list seq_elem := (
 Nor NR_DL_PRS_ResourceID_r17__Type NR_DL_PRS_ResourceID_r17__cond ::
 Nor Z NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__cond ::
 Nor NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__Type NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__cond ::
 Nor Z NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__cond ::
 Nor Z NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__cond ::
 Opt DL_PRS_QCL_Info_r17__Type DL_PRS_QCL_Info_r17__cond ::
 nil).
Definition NR_DL_PRS_Resource_r17__ext_list : list typ := (
  nil).
Definition NR_DL_PRS_Resource_r17__cond (z : NR_DL_PRS_Resource_r17__Type) := 
(  NR_DL_PRS_ResourceID_r17__cond (NR_DL_PRS_Resource_r17__nr_DL_PRS_ResourceID_r17 z) /\
  NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__cond (NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17 z) /\
  NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__cond (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17 z) /\
  NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__cond (NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17 z) /\
  NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__cond (NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17 z) /\
  opt_cond DL_PRS_QCL_Info_r17__cond (NR_DL_PRS_Resource_r17__dl_PRS_QCL_Info_r17 z) /\
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
Definition NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__Format : T_Format Z NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__cond :=
 ranged_int_format (0) (4095) NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__helper1 NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__helper2.

Opaque NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__cond NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__Format.

Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__Format : T_Format Z NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__cond :=
 ranged_int_format (0) (1) NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__helper1 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__helper2.

Opaque NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__Format.

Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__Format : T_Format Z NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__cond :=
 ranged_int_format (0) (3) NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__helper1 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__helper2.

Opaque NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__Format.

Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__Format : T_Format Z NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__cond :=
 ranged_int_format (0) (5) NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__helper1 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__helper2.

Opaque NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__Format.

Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__Format : T_Format Z NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__cond :=
 ranged_int_format (0) (11) NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__helper1 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__helper2.

Opaque NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__Format.


Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Format_Type := Eval cbn in get_formats NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Format_list : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Format_Type :=
  (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17__Format, (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17__Format, (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17__Format, (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17__Format, unit__Format)))).
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list__Format := Eval compute in choice_format NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__len_helper1 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__len_helper2  NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Format_list.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F1 (z : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type) : (choice NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list) :=
  match z with
   | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17 t => existT _ 0 t
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17 t => existT _ 1 t
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17 t => existT _ 2 t
  | NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17 t => existT _ 3 t
  end.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__g := (fun n => typ_set (get_nth_typ NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list n)).
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F2 (y : choice NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list) : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__g n -> NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type) with
    | 0 => fun (t : Z) => NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n2_r17 t 
    | 1 => fun (t : Z) => NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n4_r17 t 
    | 2 => fun (t : Z) => NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n6_r17 t 
    | 3 => fun (t : Z) => NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__n12_r17 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type with end) n0
           end t0).

Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__helper2 :  forall (y : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type), NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__cond y -> choice_cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__helper3 :  forall (y : NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type), NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F2 (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__helper4 : (forall b : choice NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list, choice_cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list b -> NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__cond (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F2 b) /\ NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F1 (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F1 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F2.
Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Format : T_Format NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Type NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__cond :=
  (* Eval compute in *) proj2_format NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__list__Format NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F1 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__F2 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__helper2 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__helper3 NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__helper4.
Opaque NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Format.

Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__Format : T_Format NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__Type NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__cond := empty_format.
Opaque NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__Format.

Definition NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__Format : T_Format NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__Type NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__cond := sum_format NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__root__Format NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__ext__Format.
Opaque NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__cond NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__Format.

Definition NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__Format : T_Format Z NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__cond :=
 ranged_int_format (0) (maxNrofPRS_ResourceOffsetValue_1_r17) NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__helper1 NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__helper2.

Opaque NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__cond NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__Format.

Definition NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__Format : T_Format Z NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__cond :=
 ranged_int_format (0) (12) NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__helper1 NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__helper2.

Opaque NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__cond NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__Format.


Definition NR_DL_PRS_Resource_r17__root_Format_Type := Eval cbn in seq_format_prod NR_DL_PRS_Resource_r17__root_list.
Definition NR_DL_PRS_Resource_r17__root_Format_list : NR_DL_PRS_Resource_r17__root_Format_Type :=
  (NR_DL_PRS_ResourceID_r17__Format, (NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17__Format, (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17__Format, (NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17__Format, (NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17__Format, (DL_PRS_QCL_Info_r17__Format, unit_format)))))).

Definition NR_DL_PRS_Resource_r17__ext_Format_Type := Eval cbn in get_formats NR_DL_PRS_Resource_r17__ext_list.
Definition NR_DL_PRS_Resource_r17__ext_Format_list : NR_DL_PRS_Resource_r17__ext_Format_Type :=
  unit__Format.

Definition NR_DL_PRS_Resource_r17__list_type : Set := (seq_type NR_DL_PRS_Resource_r17__root_list) * (seq_ext_type NR_DL_PRS_Resource_r17__ext_list).
Definition NR_DL_PRS_Resource_r17__list_cond (z : NR_DL_PRS_Resource_r17__list_type) : Prop :=
        (seq_cond NR_DL_PRS_Resource_r17__root_list (fst z)) /\ (seq_ext_cond NR_DL_PRS_Resource_r17__ext_list (snd z)).
Definition NR_DL_PRS_Resource_r17__list_format : T_Format NR_DL_PRS_Resource_r17__list_type NR_DL_PRS_Resource_r17__list_cond :=
 (* Eval compute in *) seq_ext_format NR_DL_PRS_Resource_r17__root_list NR_DL_PRS_Resource_r17__root_Format_list NR_DL_PRS_Resource_r17__ext_list NR_DL_PRS_Resource_r17__ext_Format_list.

Opaque NR_DL_PRS_Resource_r17__list_format.
Definition NR_DL_PRS_Resource_r17__F1 (z : NR_DL_PRS_Resource_r17__Type) : NR_DL_PRS_Resource_r17__list_type :=
  (((NR_DL_PRS_Resource_r17__nr_DL_PRS_ResourceID_r17 z, (NR_DL_PRS_Resource_r17__dl_PRS_SequenceID_r17 z, (NR_DL_PRS_Resource_r17__dl_PRS_CombSizeN_AndReOffset_r17 z, (NR_DL_PRS_Resource_r17__dl_PRS_ResourceSlotOffset_r17 z, (NR_DL_PRS_Resource_r17__dl_PRS_ResourceSymbolOffset_r17 z, (NR_DL_PRS_Resource_r17__dl_PRS_QCL_Info_r17 z, tt))))))), (
tt)).
Definition NR_DL_PRS_Resource_r17__F2 (y : NR_DL_PRS_Resource_r17__list_type) : NR_DL_PRS_Resource_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__NR_DL_PRS_Resource_r17__Type j0 j1 j2 j3 j4 j5
  end.
Definition NR_DL_PRS_Resource_r17__helper1 : (forall a : NR_DL_PRS_Resource_r17__Type, NR_DL_PRS_Resource_r17__cond a -> NR_DL_PRS_Resource_r17__list_cond (NR_DL_PRS_Resource_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NR_DL_PRS_Resource_r17__helper2 : (forall a : NR_DL_PRS_Resource_r17__Type, NR_DL_PRS_Resource_r17__F2 (NR_DL_PRS_Resource_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NR_DL_PRS_Resource_r17__helper3 : (forall b : NR_DL_PRS_Resource_r17__list_type, NR_DL_PRS_Resource_r17__list_cond b -> NR_DL_PRS_Resource_r17__cond (NR_DL_PRS_Resource_r17__F2 b) /\ NR_DL_PRS_Resource_r17__F1 (NR_DL_PRS_Resource_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NR_DL_PRS_Resource_r17__cond, NR_DL_PRS_Resource_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NR_DL_PRS_Resource_r17__Format : T_Format NR_DL_PRS_Resource_r17__Type NR_DL_PRS_Resource_r17__cond :=
 proj2_format NR_DL_PRS_Resource_r17__cond NR_DL_PRS_Resource_r17__list_format  NR_DL_PRS_Resource_r17__F1 NR_DL_PRS_Resource_r17__F2 NR_DL_PRS_Resource_r17__helper1 NR_DL_PRS_Resource_r17__helper2 NR_DL_PRS_Resource_r17__helper3.

Opaque NR_DL_PRS_Resource_r17__cond NR_DL_PRS_Resource_r17__Format.

