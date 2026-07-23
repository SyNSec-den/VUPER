Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__cond := (fun z => (0 <= z <= 4)%Z).
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__cond := (fun z => (0 <= z <= 9)%Z).
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__cond := (fun z => (0 <= z <= 19)%Z).
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__cond := (fun z => (0 <= z <= 39)%Z).
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__cond := (fun z => (0 <= z <= 79)%Z).
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__cond := (fun z => (0 <= z <= 159)%Z).
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__cond := (fun z => (0 <= z <= 319)%Z).
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__cond := (fun z => (0 <= z <= 639)%Z).
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__Type := Z.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__cond := (fun z => (0 <= z <= 1279)%Z).

Inductive SSB_MTC3_r16__periodicityAndOffset_r16__Type : Set :=
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16 : Z -> SSB_MTC3_r16__periodicityAndOffset_r16__Type
.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__list : list typ := (
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__cond ::
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__cond ::
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__cond ::
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__cond ::
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__cond ::
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__cond ::
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__cond ::
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__cond ::
typ_cons Z SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__cond ::
 nil).
Definition SSB_MTC3_r16__periodicityAndOffset_r16__cond (c : SSB_MTC3_r16__periodicityAndOffset_r16__Type) := 
  match c with
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__cond t 
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__cond t 
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__cond t 
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__cond t 
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__cond t 
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__cond t 
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__cond t 
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__cond t 
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16 t => SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__cond t 
  end.

Lemma SSB_MTC3_r16__periodicityAndOffset_r16__len_helper1 : to_bit_sz (length SSB_MTC3_r16__periodicityAndOffset_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__len_helper2 : 2 <= length2 SSB_MTC3_r16__periodicityAndOffset_r16__list.
 simpl. lia. Qed.
Inductive SSB_MTC3_r16__duration_r16__Type : Set :=
 | SSB_MTC3_r16__duration_r16__sf1
 | SSB_MTC3_r16__duration_r16__sf2
 | SSB_MTC3_r16__duration_r16__sf3
 | SSB_MTC3_r16__duration_r16__sf4
 | SSB_MTC3_r16__duration_r16__sf5
.
Definition SSB_MTC3_r16__duration_r16__cond := (fun (_ : SSB_MTC3_r16__duration_r16__Type) => True).
Lemma SSB_MTC3_r16__duration_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SSB_MTC3_r16__duration_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SSB_MTC3_r16__duration_r16__nat__helper.

Definition SSB_MTC3_r16__duration_r16__F1 t :=
  match t with
  | SSB_MTC3_r16__duration_r16__sf1 => 0
  | SSB_MTC3_r16__duration_r16__sf2 => 1
  | SSB_MTC3_r16__duration_r16__sf3 => 2
  | SSB_MTC3_r16__duration_r16__sf4 => 3
  | SSB_MTC3_r16__duration_r16__sf5 => 4
  end.
Definition SSB_MTC3_r16__duration_r16__F2 n :=
  match n with
  | 0 => SSB_MTC3_r16__duration_r16__sf1
  | 1 => SSB_MTC3_r16__duration_r16__sf2
  | 2 => SSB_MTC3_r16__duration_r16__sf3
  | 3 => SSB_MTC3_r16__duration_r16__sf4
  | 4 => SSB_MTC3_r16__duration_r16__sf5
  | _ => SSB_MTC3_r16__duration_r16__sf1
  end.
Lemma SSB_MTC3_r16__duration_r16__F1F2 : forall x : SSB_MTC3_r16__duration_r16__Type, (SSB_MTC3_r16__duration_r16__F1 x <= 4) /\ SSB_MTC3_r16__duration_r16__F2 (SSB_MTC3_r16__duration_r16__F1 x) = x. imp_solve. Qed.
Lemma SSB_MTC3_r16__duration_r16__F2F1 : forall (y : nat) (H : y <= 4), SSB_MTC3_r16__duration_r16__F1 (SSB_MTC3_r16__duration_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Definition SSB_MTC3_r16__pci_List_r16__Type := list PhysCellId__Type.

Lemma SSB_MTC3_r16__pci_List_r16__helper1 : (0 <= 1 <= maxNrofPCIsPerSMTC)%Z. unfold maxNrofPCIsPerSMTC.
 lia. Qed.
Lemma SSB_MTC3_r16__pci_List_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPCIsPerSMTC - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPCIsPerSMTC - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SSB_MTC3_r16__pci_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SSB_MTC3_r16__pci_List_r16__cond (z : SSB_MTC3_r16__pci_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPCIsPerSMTC)%Z /\ (list_and PhysCellId__cond z) .

Require Import NR.SetupRelease.
Require Import NR.SSB_ToMeasure.
Definition SSB_MTC3_r16__ssb_ToMeasure_r16__Type := SetupRelease__Type SSB_ToMeasure__Type.
Definition SSB_MTC3_r16__ssb_ToMeasure_r16__cond := SetupRelease__cond _ SSB_ToMeasure__cond.
Definition SSB_MTC3_r16__ssb_ToMeasure_r16__Format : T_Format SSB_MTC3_r16__ssb_ToMeasure_r16__Type SSB_MTC3_r16__ssb_ToMeasure_r16__cond := SetupRelease__Format _ _ SSB_ToMeasure__Format.
Opaque SSB_MTC3_r16__ssb_ToMeasure_r16__cond SSB_MTC3_r16__ssb_ToMeasure_r16__Format.

Record SSB_MTC3_r16__Type : Set :=
  make__SSB_MTC3_r16__Type {
    SSB_MTC3_r16__periodicityAndOffset_r16 : SSB_MTC3_r16__periodicityAndOffset_r16__Type ;
    SSB_MTC3_r16__duration_r16 : SSB_MTC3_r16__duration_r16__Type ;
    SSB_MTC3_r16__pci_List_r16 : option SSB_MTC3_r16__pci_List_r16__Type ;
    SSB_MTC3_r16__ssb_ToMeasure_r16 : option SSB_MTC3_r16__ssb_ToMeasure_r16__Type ;
}.
Definition SSB_MTC3_r16__list := (
 Nor SSB_MTC3_r16__periodicityAndOffset_r16__Type SSB_MTC3_r16__periodicityAndOffset_r16__cond ::
 Nor SSB_MTC3_r16__duration_r16__Type SSB_MTC3_r16__duration_r16__cond ::
 Opt SSB_MTC3_r16__pci_List_r16__Type SSB_MTC3_r16__pci_List_r16__cond ::
 Opt SSB_MTC3_r16__ssb_ToMeasure_r16__Type SSB_MTC3_r16__ssb_ToMeasure_r16__cond ::
 nil).
Definition SSB_MTC3_r16__cond z := 
  SSB_MTC3_r16__periodicityAndOffset_r16__cond (SSB_MTC3_r16__periodicityAndOffset_r16 z) /\
  SSB_MTC3_r16__duration_r16__cond (SSB_MTC3_r16__duration_r16 z) /\
  opt_cond SSB_MTC3_r16__pci_List_r16__cond (SSB_MTC3_r16__pci_List_r16 z) /\
  opt_cond SSB_MTC3_r16__ssb_ToMeasure_r16__cond (SSB_MTC3_r16__ssb_ToMeasure_r16 z) /\
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
Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__cond :=
 ranged_int_format (0) (4) SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__Format.

Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__cond :=
 ranged_int_format (0) (9) SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__Format.

Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__cond :=
 ranged_int_format (0) (19) SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__Format.

Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__cond :=
 ranged_int_format (0) (39) SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__Format.

Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__cond :=
 ranged_int_format (0) (79) SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__Format.

Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__cond :=
 ranged_int_format (0) (159) SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__Format.

Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__cond :=
 ranged_int_format (0) (319) SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__Format.

Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__cond :=
 ranged_int_format (0) (639) SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__Format.

Definition SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__Format : T_Format Z SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__cond :=
 ranged_int_format (0) (1279) SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__helper1 SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__helper2.

Opaque SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__Format.


Definition SSB_MTC3_r16__periodicityAndOffset_r16__Format_Type := Eval cbn in get_formats SSB_MTC3_r16__periodicityAndOffset_r16__list.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__Format_list : SSB_MTC3_r16__periodicityAndOffset_r16__Format_Type :=
  (SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16__Format, (SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16__Format, (SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16__Format, (SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16__Format, (SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16__Format, (SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16__Format, (SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16__Format, (SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16__Format, (SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16__Format, unit__Format))))))))).
Definition SSB_MTC3_r16__periodicityAndOffset_r16__list__Format := Eval compute in choice_format SSB_MTC3_r16__periodicityAndOffset_r16__list SSB_MTC3_r16__periodicityAndOffset_r16__len_helper1 SSB_MTC3_r16__periodicityAndOffset_r16__len_helper2  SSB_MTC3_r16__periodicityAndOffset_r16__Format_list.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__F1 (z : SSB_MTC3_r16__periodicityAndOffset_r16__Type) : (choice SSB_MTC3_r16__periodicityAndOffset_r16__list) :=
  match z with
   | SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16 t => existT _ 0 t
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16 t => existT _ 1 t
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16 t => existT _ 2 t
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16 t => existT _ 3 t
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16 t => existT _ 4 t
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16 t => existT _ 5 t
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16 t => existT _ 6 t
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16 t => existT _ 7 t
  | SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16 t => existT _ 8 t
  end.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__g := (fun n => typ_set (get_nth_typ SSB_MTC3_r16__periodicityAndOffset_r16__list n)).
Definition SSB_MTC3_r16__periodicityAndOffset_r16__F2 (y : choice SSB_MTC3_r16__periodicityAndOffset_r16__list) : SSB_MTC3_r16__periodicityAndOffset_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SSB_MTC3_r16__periodicityAndOffset_r16__g n -> SSB_MTC3_r16__periodicityAndOffset_r16__Type) with
    | 0 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf5_r16 t 
    | 1 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf10_r16 t 
    | 2 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf20_r16 t 
    | 3 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf40_r16 t 
    | 4 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf80_r16 t 
    | 5 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf160_r16 t 
    | 6 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf320_r16 t 
    | 7 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf640_r16 t 
    | 8 => fun (t : Z) => SSB_MTC3_r16__periodicityAndOffset_r16__sf1280_r16 t 
 | (S (S (S (S (S (S (S (S (S n0))))))))) => (fun (x' : nat) (t'' : SSB_MTC3_r16__periodicityAndOffset_r16__g (S (S (S (S (S (S (S (S (S x')))))))))) =>let t' :=
           eq_rect (get_nth_typ SSB_MTC3_r16__periodicityAndOffset_r16__list (S (S (S (S (S (S (S (S (S x'))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SSB_MTC3_r16__periodicityAndOffset_r16__list (S (S (S (S (S (S (S (S (S x')))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))) in match t' return SSB_MTC3_r16__periodicityAndOffset_r16__Type with end) n0
           end t0).

Lemma SSB_MTC3_r16__periodicityAndOffset_r16__helper2 :  forall (y : SSB_MTC3_r16__periodicityAndOffset_r16__Type), SSB_MTC3_r16__periodicityAndOffset_r16__cond y -> choice_cond SSB_MTC3_r16__periodicityAndOffset_r16__list (SSB_MTC3_r16__periodicityAndOffset_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SSB_MTC3_r16__periodicityAndOffset_r16__helper3 :  forall (y : SSB_MTC3_r16__periodicityAndOffset_r16__Type), SSB_MTC3_r16__periodicityAndOffset_r16__F2 (SSB_MTC3_r16__periodicityAndOffset_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SSB_MTC3_r16__periodicityAndOffset_r16__helper4 : (forall b : choice SSB_MTC3_r16__periodicityAndOffset_r16__list, choice_cond SSB_MTC3_r16__periodicityAndOffset_r16__list b -> SSB_MTC3_r16__periodicityAndOffset_r16__cond (SSB_MTC3_r16__periodicityAndOffset_r16__F2 b) /\ SSB_MTC3_r16__periodicityAndOffset_r16__F1 (SSB_MTC3_r16__periodicityAndOffset_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SSB_MTC3_r16__periodicityAndOffset_r16__F1 SSB_MTC3_r16__periodicityAndOffset_r16__F2.
Definition SSB_MTC3_r16__periodicityAndOffset_r16__Format : T_Format SSB_MTC3_r16__periodicityAndOffset_r16__Type SSB_MTC3_r16__periodicityAndOffset_r16__cond :=
  (* Eval compute in *) proj2_format SSB_MTC3_r16__periodicityAndOffset_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__list__Format SSB_MTC3_r16__periodicityAndOffset_r16__F1 SSB_MTC3_r16__periodicityAndOffset_r16__F2 SSB_MTC3_r16__periodicityAndOffset_r16__helper2 SSB_MTC3_r16__periodicityAndOffset_r16__helper3 SSB_MTC3_r16__periodicityAndOffset_r16__helper4.
Opaque SSB_MTC3_r16__periodicityAndOffset_r16__cond SSB_MTC3_r16__periodicityAndOffset_r16__Format.

Definition SSB_MTC3_r16__duration_r16__Format : T_Format SSB_MTC3_r16__duration_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SSB_MTC3_r16__duration_r16__nat__Format SSB_MTC3_r16__duration_r16__F1 SSB_MTC3_r16__duration_r16__F2 SSB_MTC3_r16__duration_r16__F1F2 SSB_MTC3_r16__duration_r16__F2F1.

Opaque SSB_MTC3_r16__duration_r16__cond SSB_MTC3_r16__duration_r16__Format.

Definition SSB_MTC3_r16__pci_List_r16__Format : T_Format SSB_MTC3_r16__pci_List_r16__Type SSB_MTC3_r16__pci_List_r16__cond := seq_of_format PhysCellId__Format 1 maxNrofPCIsPerSMTC SSB_MTC3_r16__pci_List_r16__helper1 SSB_MTC3_r16__pci_List_r16__helper2.

Opaque SSB_MTC3_r16__pci_List_r16__cond SSB_MTC3_r16__pci_List_r16__Format.

Opaque SSB_MTC3_r16__ssb_ToMeasure_r16__cond SSB_MTC3_r16__ssb_ToMeasure_r16__Format.


Definition SSB_MTC3_r16__Format_Type := Eval cbn in seq_format_prod SSB_MTC3_r16__list.
Definition SSB_MTC3_r16__Format_list : SSB_MTC3_r16__Format_Type :=
  (SSB_MTC3_r16__periodicityAndOffset_r16__Format, (SSB_MTC3_r16__duration_r16__Format, (SSB_MTC3_r16__pci_List_r16__Format, (SSB_MTC3_r16__ssb_ToMeasure_r16__Format, unit_format)))).
Definition SSB_MTC3_r16__list__Format := (*Eval compute in *) seq_format SSB_MTC3_r16__list SSB_MTC3_r16__Format_list.
Definition SSB_MTC3_r16__F1 z :=
  (SSB_MTC3_r16__periodicityAndOffset_r16 z, (SSB_MTC3_r16__duration_r16 z, (SSB_MTC3_r16__pci_List_r16 z, (SSB_MTC3_r16__ssb_ToMeasure_r16 z, tt)))).
Definition SSB_MTC3_r16__F2 (y : seq_type SSB_MTC3_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SSB_MTC3_r16__Type i0 i1 i2 i3
  end.
Lemma SSB_MTC3_r16__F1F2_cond (z : SSB_MTC3_r16__Type)
  : SSB_MTC3_r16__cond z ->
  (seq_cond SSB_MTC3_r16__list (SSB_MTC3_r16__F1 z)).
intro H. unfold SSB_MTC3_r16__cond in H. simpl. auto. Qed.
Lemma SSB_MTC3_r16__F1F2_cond2 (z : SSB_MTC3_r16__Type)
 : SSB_MTC3_r16__F2 (SSB_MTC3_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SSB_MTC3_r16__F2F1_cond (y : seq_type SSB_MTC3_r16__list)
  : seq_cond SSB_MTC3_r16__list y ->
 (SSB_MTC3_r16__cond (SSB_MTC3_r16__F2 y)) /\  SSB_MTC3_r16__F1 (SSB_MTC3_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SSB_MTC3_r16__cond. simpl in *. auto.
 - simpl. unfold SSB_MTC3_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SSB_MTC3_r16__Format : T_Format SSB_MTC3_r16__Type SSB_MTC3_r16__cond :=
        proj2_format  SSB_MTC3_r16__cond SSB_MTC3_r16__list__Format
    SSB_MTC3_r16__F1 SSB_MTC3_r16__F2 SSB_MTC3_r16__F1F2_cond  SSB_MTC3_r16__F1F2_cond2 SSB_MTC3_r16__F2F1_cond.
Opaque SSB_MTC3_r16__cond SSB_MTC3_r16__Format.

