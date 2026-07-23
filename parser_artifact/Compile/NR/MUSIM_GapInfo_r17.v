Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MUSIM_Starting_SFN_AndSubframe_r17.

Opaque MUSIM_Starting_SFN_AndSubframe_r17__cond MUSIM_Starting_SFN_AndSubframe_r17__Format.

Inductive MUSIM_GapInfo_r17__musim_GapLength_r17__Type : Set :=
 | MUSIM_GapInfo_r17__musim_GapLength_r17__ms3
 | MUSIM_GapInfo_r17__musim_GapLength_r17__ms4
 | MUSIM_GapInfo_r17__musim_GapLength_r17__ms6
 | MUSIM_GapInfo_r17__musim_GapLength_r17__ms10
 | MUSIM_GapInfo_r17__musim_GapLength_r17__ms20
.
Definition MUSIM_GapInfo_r17__musim_GapLength_r17__cond := (fun (_ : MUSIM_GapInfo_r17__musim_GapLength_r17__Type) => True).
Lemma MUSIM_GapInfo_r17__musim_GapLength_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MUSIM_GapInfo_r17__musim_GapLength_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MUSIM_GapInfo_r17__musim_GapLength_r17__nat__helper.

Definition MUSIM_GapInfo_r17__musim_GapLength_r17__F1 t :=
  match t with
  | MUSIM_GapInfo_r17__musim_GapLength_r17__ms3 => 0
  | MUSIM_GapInfo_r17__musim_GapLength_r17__ms4 => 1
  | MUSIM_GapInfo_r17__musim_GapLength_r17__ms6 => 2
  | MUSIM_GapInfo_r17__musim_GapLength_r17__ms10 => 3
  | MUSIM_GapInfo_r17__musim_GapLength_r17__ms20 => 4
  end.
Definition MUSIM_GapInfo_r17__musim_GapLength_r17__F2 n :=
  match n with
  | 0 => MUSIM_GapInfo_r17__musim_GapLength_r17__ms3
  | 1 => MUSIM_GapInfo_r17__musim_GapLength_r17__ms4
  | 2 => MUSIM_GapInfo_r17__musim_GapLength_r17__ms6
  | 3 => MUSIM_GapInfo_r17__musim_GapLength_r17__ms10
  | 4 => MUSIM_GapInfo_r17__musim_GapLength_r17__ms20
  | _ => MUSIM_GapInfo_r17__musim_GapLength_r17__ms3
  end.
Lemma MUSIM_GapInfo_r17__musim_GapLength_r17__F1F2 : forall x : MUSIM_GapInfo_r17__musim_GapLength_r17__Type, (MUSIM_GapInfo_r17__musim_GapLength_r17__F1 x <= 4) /\ MUSIM_GapInfo_r17__musim_GapLength_r17__F2 (MUSIM_GapInfo_r17__musim_GapLength_r17__F1 x) = x. imp_solve. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapLength_r17__F2F1 : forall (y : nat) (H : y <= 4), MUSIM_GapInfo_r17__musim_GapLength_r17__F1 (MUSIM_GapInfo_r17__musim_GapLength_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__cond := (fun z => (0 <= z <= 19)%Z).
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__cond := (fun z => (0 <= z <= 39)%Z).
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__cond := (fun z => (0 <= z <= 79)%Z).
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__cond := (fun z => (0 <= z <= 159)%Z).
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__cond := (fun z => (0 <= z <= 319)%Z).
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__cond := (fun z => (0 <= z <= 639)%Z).
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__Type := Z.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__cond := (fun z => (0 <= z <= 5119)%Z).

Inductive MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type : Set :=
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17 : Z -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type
.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list : list typ := (
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__cond ::
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__cond ::
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__cond ::
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__cond ::
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__cond ::
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__cond ::
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__cond ::
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__cond ::
typ_cons Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__cond ::
 nil).
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__cond (c : MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type) := 
  match c with
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__cond t 
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__cond t 
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__cond t 
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__cond t 
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__cond t 
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__cond t 
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__cond t 
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__cond t 
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17 t => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__cond t 
  end.

Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__len_helper1 : to_bit_sz (length MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__len_helper2 : 2 <= length2 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list.
 simpl. lia. Qed.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Type : Set := Empty_set.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__cond (c : MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Type) := True.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Type : Set := MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type + MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Type.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__cond :=
  sum_cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__cond.
Record MUSIM_GapInfo_r17__Type : Set :=
  make__MUSIM_GapInfo_r17__Type {
    MUSIM_GapInfo_r17__musim_Starting_SFN_AndSubframe_r17 : option MUSIM_Starting_SFN_AndSubframe_r17__Type ;
    MUSIM_GapInfo_r17__musim_GapLength_r17 : option MUSIM_GapInfo_r17__musim_GapLength_r17__Type ;
    MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17 : option MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Type ;
}.
Definition MUSIM_GapInfo_r17__list := (
 Opt MUSIM_Starting_SFN_AndSubframe_r17__Type MUSIM_Starting_SFN_AndSubframe_r17__cond ::
 Opt MUSIM_GapInfo_r17__musim_GapLength_r17__Type MUSIM_GapInfo_r17__musim_GapLength_r17__cond ::
 Opt MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Type MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__cond ::
 nil).
Definition MUSIM_GapInfo_r17__cond z := 
  opt_cond MUSIM_Starting_SFN_AndSubframe_r17__cond (MUSIM_GapInfo_r17__musim_Starting_SFN_AndSubframe_r17 z) /\
  opt_cond MUSIM_GapInfo_r17__musim_GapLength_r17__cond (MUSIM_GapInfo_r17__musim_GapLength_r17 z) /\
  opt_cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__cond (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17 z) /\
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
Definition MUSIM_GapInfo_r17__musim_GapLength_r17__Format : T_Format MUSIM_GapInfo_r17__musim_GapLength_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MUSIM_GapInfo_r17__musim_GapLength_r17__nat__Format MUSIM_GapInfo_r17__musim_GapLength_r17__F1 MUSIM_GapInfo_r17__musim_GapLength_r17__F2 MUSIM_GapInfo_r17__musim_GapLength_r17__F1F2 MUSIM_GapInfo_r17__musim_GapLength_r17__F2F1.

Opaque MUSIM_GapInfo_r17__musim_GapLength_r17__cond MUSIM_GapInfo_r17__musim_GapLength_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__cond :=
 ranged_int_format (0) (19) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__cond :=
 ranged_int_format (0) (39) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__cond :=
 ranged_int_format (0) (79) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__cond :=
 ranged_int_format (0) (159) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__cond :=
 ranged_int_format (0) (319) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__cond :=
 ranged_int_format (0) (639) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__cond :=
 ranged_int_format (0) (1279) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__cond :=
 ranged_int_format (0) (2559) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__Format : T_Format Z MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__cond :=
 ranged_int_format (0) (5119) MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__helper2.

Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__Format.


Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Format_Type := Eval cbn in get_formats MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Format_list : MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Format_Type :=
  (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17__Format, unit__Format))))))))).
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list__Format := Eval compute in choice_format MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__len_helper1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__len_helper2  MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Format_list.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F1 (z : MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type) : (choice MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list) :=
  match z with
   | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17 t => existT _ 0 t
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17 t => existT _ 1 t
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17 t => existT _ 2 t
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17 t => existT _ 3 t
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17 t => existT _ 4 t
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17 t => existT _ 5 t
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17 t => existT _ 6 t
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17 t => existT _ 7 t
  | MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17 t => existT _ 8 t
  end.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__g := (fun n => typ_set (get_nth_typ MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list n)).
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F2 (y : choice MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list) : MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__g n -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type) with
    | 0 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms20_r17 t 
    | 1 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms40_r17 t 
    | 2 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms80_r17 t 
    | 3 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms160_r17 t 
    | 4 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms320_r17 t 
    | 5 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms640_r17 t 
    | 6 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms1280_r17 t 
    | 7 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms2560_r17 t 
    | 8 => fun (t : Z) => MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__ms5120_r17 t 
 | (S (S (S (S (S (S (S (S (S n0))))))))) => (fun (x' : nat) (t'' : MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__g (S (S (S (S (S (S (S (S (S x')))))))))) =>let t' :=
           eq_rect (get_nth_typ MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list (S (S (S (S (S (S (S (S (S x'))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list (S (S (S (S (S (S (S (S (S x')))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))) in match t' return MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type with end) n0
           end t0).

Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__helper2 :  forall (y : MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type), MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__cond y -> choice_cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__helper3 :  forall (y : MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type), MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F2 (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__helper4 : (forall b : choice MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list, choice_cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list b -> MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__cond (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F2 b) /\ MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F1 (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F2.
Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Format : T_Format MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Type MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__cond :=
  (* Eval compute in *) proj2_format MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__list__Format MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F1 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__F2 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__helper2 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__helper3 MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__helper4.
Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Format : T_Format MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Type MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__cond := empty_format.
Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Format.

Definition MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Format : T_Format MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Type MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__cond := sum_format MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__root__Format MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__ext__Format.
Opaque MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__cond MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Format.


Definition MUSIM_GapInfo_r17__Format_Type := Eval cbn in seq_format_prod MUSIM_GapInfo_r17__list.
Definition MUSIM_GapInfo_r17__Format_list : MUSIM_GapInfo_r17__Format_Type :=
  (MUSIM_Starting_SFN_AndSubframe_r17__Format, (MUSIM_GapInfo_r17__musim_GapLength_r17__Format, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17__Format, unit_format))).
Definition MUSIM_GapInfo_r17__list__Format := (*Eval compute in *) seq_format MUSIM_GapInfo_r17__list MUSIM_GapInfo_r17__Format_list.
Definition MUSIM_GapInfo_r17__F1 z :=
  (MUSIM_GapInfo_r17__musim_Starting_SFN_AndSubframe_r17 z, (MUSIM_GapInfo_r17__musim_GapLength_r17 z, (MUSIM_GapInfo_r17__musim_GapRepetitionAndOffset_r17 z, tt))).
Definition MUSIM_GapInfo_r17__F2 (y : seq_type MUSIM_GapInfo_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MUSIM_GapInfo_r17__Type i0 i1 i2
  end.
Lemma MUSIM_GapInfo_r17__F1F2_cond (z : MUSIM_GapInfo_r17__Type)
  : MUSIM_GapInfo_r17__cond z ->
  (seq_cond MUSIM_GapInfo_r17__list (MUSIM_GapInfo_r17__F1 z)).
intro H. unfold MUSIM_GapInfo_r17__cond in H. simpl. auto. Qed.
Lemma MUSIM_GapInfo_r17__F1F2_cond2 (z : MUSIM_GapInfo_r17__Type)
 : MUSIM_GapInfo_r17__F2 (MUSIM_GapInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MUSIM_GapInfo_r17__F2F1_cond (y : seq_type MUSIM_GapInfo_r17__list)
  : seq_cond MUSIM_GapInfo_r17__list y ->
 (MUSIM_GapInfo_r17__cond (MUSIM_GapInfo_r17__F2 y)) /\  MUSIM_GapInfo_r17__F1 (MUSIM_GapInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MUSIM_GapInfo_r17__cond. simpl in *. auto.
 - simpl. unfold MUSIM_GapInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MUSIM_GapInfo_r17__Format : T_Format MUSIM_GapInfo_r17__Type MUSIM_GapInfo_r17__cond :=
        proj2_format  MUSIM_GapInfo_r17__cond MUSIM_GapInfo_r17__list__Format
    MUSIM_GapInfo_r17__F1 MUSIM_GapInfo_r17__F2 MUSIM_GapInfo_r17__F1F2_cond  MUSIM_GapInfo_r17__F1F2_cond2 MUSIM_GapInfo_r17__F2F1_cond.
Opaque MUSIM_GapInfo_r17__cond MUSIM_GapInfo_r17__Format.

