Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__cond := (fun z => (0 <= z <= 3)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__cond := (fun z => (0 <= z <= 4)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__cond := (fun z => (0 <= z <= 7)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__cond := (fun z => (0 <= z <= 9)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__cond := (fun z => (0 <= z <= 15)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__cond := (fun z => (0 <= z <= 19)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__cond := (fun z => (0 <= z <= 31)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__cond := (fun z => (0 <= z <= 39)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__cond := (fun z => (0 <= z <= 63)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__cond := (fun z => (0 <= z <= 79)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__cond := (fun z => (0 <= z <= 159)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__cond := (fun z => (0 <= z <= 319)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__cond := (fun z => (0 <= z <= 639)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__cond := (fun z => (0 <= z <= 10239)%Z).

Inductive NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type : Set :=
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type
.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list : list typ := (
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__cond ::
 nil).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type) := 
  match c with
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__cond t 
  end.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__len_helper1 : to_bit_sz (length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__len_helper2 : 2 <= length2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list.
 simpl. lia. Qed.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__Type : Set := Empty_set.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__Type) := True.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__Type : Set := NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type + NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__Type.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__cond :=
  sum_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__cond.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__cond := (fun z => (0 <= z <= 7)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__cond := (fun z => (0 <= z <= 9)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__cond := (fun z => (0 <= z <= 15)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__cond := (fun z => (0 <= z <= 19)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__cond := (fun z => (0 <= z <= 31)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__cond := (fun z => (0 <= z <= 39)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__cond := (fun z => (0 <= z <= 63)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__cond := (fun z => (0 <= z <= 79)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__cond := (fun z => (0 <= z <= 127)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__cond := (fun z => (0 <= z <= 159)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__cond := (fun z => (0 <= z <= 319)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__cond := (fun z => (0 <= z <= 639)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__cond := (fun z => (0 <= z <= 10239)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__helper1 : (0 <= 20479)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__helper2 : to_bit_sz (Z.to_nat (20479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__cond := (fun z => (0 <= z <= 20479)%Z).

Inductive NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type : Set :=
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type
.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list : list typ := (
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__cond ::
 nil).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type) := 
  match c with
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__cond t 
  end.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__len_helper1 : to_bit_sz (length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__len_helper2 : 2 <= length2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list.
 simpl. lia. Qed.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__Type : Set := Empty_set.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__Type) := True.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__Type : Set := NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type + NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__Type.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__cond :=
  sum_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__cond.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__cond := (fun z => (0 <= z <= 15)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__cond := (fun z => (0 <= z <= 19)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__cond := (fun z => (0 <= z <= 31)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__cond := (fun z => (0 <= z <= 39)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__cond := (fun z => (0 <= z <= 63)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__cond := (fun z => (0 <= z <= 79)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__cond := (fun z => (0 <= z <= 127)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__cond := (fun z => (0 <= z <= 159)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__cond := (fun z => (0 <= z <= 255)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__cond := (fun z => (0 <= z <= 319)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__cond := (fun z => (0 <= z <= 639)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__cond := (fun z => (0 <= z <= 10239)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__helper1 : (0 <= 20479)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__helper2 : to_bit_sz (Z.to_nat (20479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__cond := (fun z => (0 <= z <= 20479)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__helper1 : (0 <= 40959)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__helper2 : to_bit_sz (Z.to_nat (40959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__cond := (fun z => (0 <= z <= 40959)%Z).

Inductive NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type : Set :=
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type
.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list : list typ := (
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__cond ::
 nil).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type) := 
  match c with
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__cond t 
  end.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__len_helper1 : to_bit_sz (length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__len_helper2 : 2 <= length2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list.
 simpl. lia. Qed.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__Type : Set := Empty_set.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__Type) := True.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__Type : Set := NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type + NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__Type.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__cond :=
  sum_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__cond.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__cond := (fun z => (0 <= z <= 31)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__cond := (fun z => (0 <= z <= 39)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__cond := (fun z => (0 <= z <= 63)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__cond := (fun z => (0 <= z <= 79)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__cond := (fun z => (0 <= z <= 127)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__cond := (fun z => (0 <= z <= 159)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__cond := (fun z => (0 <= z <= 255)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__cond := (fun z => (0 <= z <= 319)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__helper1 : (0 <= 511)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__helper2 : to_bit_sz (Z.to_nat (511 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (511 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__cond := (fun z => (0 <= z <= 511)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__cond := (fun z => (0 <= z <= 639)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__cond := (fun z => (0 <= z <= 10239)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__helper1 : (0 <= 20479)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__helper2 : to_bit_sz (Z.to_nat (20479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__cond := (fun z => (0 <= z <= 20479)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__helper1 : (0 <= 40959)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__helper2 : to_bit_sz (Z.to_nat (40959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__cond := (fun z => (0 <= z <= 40959)%Z).
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__helper1 : (0 <= 81919)%Z.  lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__helper2 : to_bit_sz (Z.to_nat (81919 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (81919 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__Type := Z.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__cond := (fun z => (0 <= z <= 81919)%Z).

Inductive NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type : Set :=
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17 : Z -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type
.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list : list typ := (
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__cond ::
typ_cons Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__cond ::
 nil).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type) := 
  match c with
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__cond t 
  end.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__len_helper1 : to_bit_sz (length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__len_helper2 : 2 <= length2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list.
 simpl. lia. Qed.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__Type : Set := Empty_set.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__Type) := True.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__Type : Set := NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type + NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__Type.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__cond :=
  sum_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__cond.

Inductive NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type : Set :=
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17 : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__Type -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17 : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__Type -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17 : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__Type -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17 : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__Type -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type
.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list : list typ := (
typ_cons NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__cond ::
typ_cons NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__cond ::
typ_cons NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__cond ::
typ_cons NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__cond ::
 nil).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type) := 
  match c with
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__cond t 
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17 t => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__cond t 
  end.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__len_helper1 : to_bit_sz (length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__len_helper2 : 2 <= length2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list.
 simpl. lia. Qed.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__Type : Set := Empty_set.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__cond (c : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__Type) := True.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__Type : Set := NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type + NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__Type.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__cond :=
  sum_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__cond.

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
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__cond :=
 ranged_int_format (0) (3) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__cond :=
 ranged_int_format (0) (4) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__cond :=
 ranged_int_format (0) (7) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__cond :=
 ranged_int_format (0) (9) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__cond :=
 ranged_int_format (0) (15) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__cond :=
 ranged_int_format (0) (19) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__cond :=
 ranged_int_format (0) (31) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__cond :=
 ranged_int_format (0) (39) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__cond :=
 ranged_int_format (0) (63) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__cond :=
 ranged_int_format (0) (79) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__cond :=
 ranged_int_format (0) (159) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__cond :=
 ranged_int_format (0) (319) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__cond :=
 ranged_int_format (0) (639) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__cond :=
 ranged_int_format (0) (1279) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__cond :=
 ranged_int_format (0) (2559) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__cond :=
 ranged_int_format (0) (5119) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__cond :=
 ranged_int_format (0) (10239) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__Format.


Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Format_Type := Eval cbn in get_formats NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Format_list : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Format_Type :=
  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17__Format, unit__Format))))))))))))))))).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list__Format := Eval compute in choice_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__len_helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__len_helper2  NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Format_list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F1 (z : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type) : (choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list) :=
  match z with
   | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17 t => existT _ 0 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17 t => existT _ 1 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17 t => existT _ 2 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17 t => existT _ 3 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17 t => existT _ 4 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17 t => existT _ 5 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17 t => existT _ 6 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17 t => existT _ 7 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17 t => existT _ 8 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17 t => existT _ 9 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17 t => existT _ 10 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17 t => existT _ 11 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17 t => existT _ 12 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17 t => existT _ 13 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17 t => existT _ 14 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17 t => existT _ 15 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17 t => existT _ 16 t
  end.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__g := (fun n => typ_set (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list n)).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F2 (y : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list) : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__g n -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type) with
    | 0 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n4_r17 t 
    | 1 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5_r17 t 
    | 2 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n8_r17 t 
    | 3 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10_r17 t 
    | 4 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n16_r17 t 
    | 5 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n20_r17 t 
    | 6 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n32_r17 t 
    | 7 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n40_r17 t 
    | 8 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n64_r17 t 
    | 9 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n80_r17 t 
    | 10 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n160_r17 t 
    | 11 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n320_r17 t 
    | 12 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n640_r17 t 
    | 13 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n1280_r17 t 
    | 14 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n2560_r17 t 
    | 15 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n5120_r17 t 
    | 16 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__n10240_r17 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))) => (fun (x' : nat) (t'' : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))) in match t' return NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type with end) n0
           end t0).

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__helper2 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__cond y -> choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__helper3 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F2 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__helper4 : (forall b : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list, choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list b -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__cond (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F2 b) /\ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F1 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F2.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__cond :=
  (* Eval compute in *) proj2_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__list__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__F2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__helper2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__helper3 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__helper4.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__cond := empty_format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__cond := sum_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__root__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__ext__Format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__cond :=
 ranged_int_format (0) (7) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__cond :=
 ranged_int_format (0) (9) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__cond :=
 ranged_int_format (0) (15) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__cond :=
 ranged_int_format (0) (19) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__cond :=
 ranged_int_format (0) (31) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__cond :=
 ranged_int_format (0) (39) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__cond :=
 ranged_int_format (0) (63) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__cond :=
 ranged_int_format (0) (79) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__cond :=
 ranged_int_format (0) (127) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__cond :=
 ranged_int_format (0) (159) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__cond :=
 ranged_int_format (0) (319) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__cond :=
 ranged_int_format (0) (639) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__cond :=
 ranged_int_format (0) (1279) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__cond :=
 ranged_int_format (0) (2559) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__cond :=
 ranged_int_format (0) (5119) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__cond :=
 ranged_int_format (0) (10239) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__cond :=
 ranged_int_format (0) (20479) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__Format.


Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Format_Type := Eval cbn in get_formats NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Format_list : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Format_Type :=
  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17__Format, unit__Format))))))))))))))))).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list__Format := Eval compute in choice_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__len_helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__len_helper2  NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Format_list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F1 (z : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type) : (choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list) :=
  match z with
   | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17 t => existT _ 0 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17 t => existT _ 1 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17 t => existT _ 2 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17 t => existT _ 3 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17 t => existT _ 4 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17 t => existT _ 5 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17 t => existT _ 6 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17 t => existT _ 7 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17 t => existT _ 8 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17 t => existT _ 9 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17 t => existT _ 10 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17 t => existT _ 11 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17 t => existT _ 12 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17 t => existT _ 13 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17 t => existT _ 14 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17 t => existT _ 15 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17 t => existT _ 16 t
  end.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__g := (fun n => typ_set (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list n)).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F2 (y : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list) : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__g n -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type) with
    | 0 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n8_r17 t 
    | 1 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10_r17 t 
    | 2 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n16_r17 t 
    | 3 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20_r17 t 
    | 4 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n32_r17 t 
    | 5 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n40_r17 t 
    | 6 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n64_r17 t 
    | 7 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n80_r17 t 
    | 8 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n128_r17 t 
    | 9 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n160_r17 t 
    | 10 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n320_r17 t 
    | 11 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n640_r17 t 
    | 12 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n1280_r17 t 
    | 13 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n2560_r17 t 
    | 14 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n5120_r17 t 
    | 15 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n10240_r17 t 
    | 16 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__n20480_r17 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))) => (fun (x' : nat) (t'' : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))) in match t' return NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type with end) n0
           end t0).

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__helper2 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__cond y -> choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__helper3 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F2 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__helper4 : (forall b : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list, choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list b -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__cond (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F2 b) /\ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F1 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F2.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__cond :=
  (* Eval compute in *) proj2_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__list__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__F2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__helper2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__helper3 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__helper4.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__cond := empty_format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__cond := sum_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__root__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__ext__Format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__cond :=
 ranged_int_format (0) (15) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__cond :=
 ranged_int_format (0) (19) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__cond :=
 ranged_int_format (0) (31) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__cond :=
 ranged_int_format (0) (39) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__cond :=
 ranged_int_format (0) (63) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__cond :=
 ranged_int_format (0) (79) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__cond :=
 ranged_int_format (0) (127) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__cond :=
 ranged_int_format (0) (159) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__cond :=
 ranged_int_format (0) (255) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__cond :=
 ranged_int_format (0) (319) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__cond :=
 ranged_int_format (0) (639) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__cond :=
 ranged_int_format (0) (1279) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__cond :=
 ranged_int_format (0) (2559) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__cond :=
 ranged_int_format (0) (5119) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__cond :=
 ranged_int_format (0) (10239) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__cond :=
 ranged_int_format (0) (20479) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__cond :=
 ranged_int_format (0) (40959) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__Format.


Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Format_Type := Eval cbn in get_formats NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Format_list : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Format_Type :=
  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17__Format, unit__Format))))))))))))))))).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list__Format := Eval compute in choice_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__len_helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__len_helper2  NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Format_list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F1 (z : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type) : (choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list) :=
  match z with
   | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17 t => existT _ 0 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17 t => existT _ 1 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17 t => existT _ 2 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17 t => existT _ 3 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17 t => existT _ 4 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17 t => existT _ 5 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17 t => existT _ 6 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17 t => existT _ 7 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17 t => existT _ 8 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17 t => existT _ 9 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17 t => existT _ 10 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17 t => existT _ 11 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17 t => existT _ 12 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17 t => existT _ 13 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17 t => existT _ 14 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17 t => existT _ 15 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17 t => existT _ 16 t
  end.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__g := (fun n => typ_set (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list n)).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F2 (y : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list) : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__g n -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type) with
    | 0 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n16_r17 t 
    | 1 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20_r17 t 
    | 2 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n32_r17 t 
    | 3 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40_r17 t 
    | 4 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n64_r17 t 
    | 5 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n80_r17 t 
    | 6 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n128_r17 t 
    | 7 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n160_r17 t 
    | 8 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n256_r17 t 
    | 9 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n320_r17 t 
    | 10 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n640_r17 t 
    | 11 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n1280_r17 t 
    | 12 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n2560_r17 t 
    | 13 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n5120_r17 t 
    | 14 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n10240_r17 t 
    | 15 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n20480_r17 t 
    | 16 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__n40960_r17 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))) => (fun (x' : nat) (t'' : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))) in match t' return NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type with end) n0
           end t0).

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__helper2 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__cond y -> choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__helper3 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F2 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__helper4 : (forall b : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list, choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list b -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__cond (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F2 b) /\ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F1 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F2.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__cond :=
  (* Eval compute in *) proj2_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__list__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__F2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__helper2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__helper3 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__helper4.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__cond := empty_format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__cond := sum_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__root__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__ext__Format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__cond :=
 ranged_int_format (0) (31) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__cond :=
 ranged_int_format (0) (39) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__cond :=
 ranged_int_format (0) (63) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__cond :=
 ranged_int_format (0) (79) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__cond :=
 ranged_int_format (0) (127) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__cond :=
 ranged_int_format (0) (159) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__cond :=
 ranged_int_format (0) (255) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__cond :=
 ranged_int_format (0) (319) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__cond :=
 ranged_int_format (0) (511) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__cond :=
 ranged_int_format (0) (639) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__cond :=
 ranged_int_format (0) (1279) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__cond :=
 ranged_int_format (0) (2559) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__cond :=
 ranged_int_format (0) (5119) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__cond :=
 ranged_int_format (0) (10239) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__cond :=
 ranged_int_format (0) (20479) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__cond :=
 ranged_int_format (0) (40959) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__Format : T_Format Z NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__cond :=
 ranged_int_format (0) (81919) NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__helper2.

Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__Format.


Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Format_Type := Eval cbn in get_formats NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Format_list : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Format_Type :=
  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17__Format, unit__Format))))))))))))))))).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list__Format := Eval compute in choice_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__len_helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__len_helper2  NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Format_list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F1 (z : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type) : (choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list) :=
  match z with
   | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17 t => existT _ 0 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17 t => existT _ 1 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17 t => existT _ 2 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17 t => existT _ 3 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17 t => existT _ 4 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17 t => existT _ 5 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17 t => existT _ 6 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17 t => existT _ 7 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17 t => existT _ 8 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17 t => existT _ 9 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17 t => existT _ 10 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17 t => existT _ 11 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17 t => existT _ 12 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17 t => existT _ 13 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17 t => existT _ 14 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17 t => existT _ 15 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17 t => existT _ 16 t
  end.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__g := (fun n => typ_set (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list n)).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F2 (y : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list) : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__g n -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type) with
    | 0 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n32_r17 t 
    | 1 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40_r17 t 
    | 2 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n64_r17 t 
    | 3 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n80_r17 t 
    | 4 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n128_r17 t 
    | 5 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n160_r17 t 
    | 6 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n256_r17 t 
    | 7 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n320_r17 t 
    | 8 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n512_r17 t 
    | 9 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n640_r17 t 
    | 10 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n1280_r17 t 
    | 11 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n2560_r17 t 
    | 12 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n5120_r17 t 
    | 13 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n10240_r17 t 
    | 14 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n20480_r17 t 
    | 15 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n40960_r17 t 
    | 16 => fun (t : Z) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__n81920_r17 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))) => (fun (x' : nat) (t'' : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))) in match t' return NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type with end) n0
           end t0).

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__helper2 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__cond y -> choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__helper3 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F2 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__helper4 : (forall b : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list, choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list b -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__cond (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F2 b) /\ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F1 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F2.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__cond :=
  (* Eval compute in *) proj2_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__list__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__F2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__helper2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__helper3 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__helper4.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__cond := empty_format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__cond := sum_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__root__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__ext__Format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__Format.


Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Format_Type := Eval cbn in get_formats NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Format_list : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Format_Type :=
  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__Format, (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__Format, unit__Format)))).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list__Format := Eval compute in choice_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__len_helper1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__len_helper2  NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Format_list.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F1 (z : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type) : (choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list) :=
  match z with
   | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17 t => existT _ 0 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17 t => existT _ 1 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17 t => existT _ 2 t
  | NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17 t => existT _ 3 t
  end.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__g := (fun n => typ_set (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list n)).
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F2 (y : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list) : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__g n -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type) with
    | 0 => fun (t : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17__Type) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs15_r17 t 
    | 1 => fun (t : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17__Type) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs30_r17 t 
    | 2 => fun (t : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17__Type) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs60_r17 t 
    | 3 => fun (t : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17__Type) => NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__scs120_r17 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type with end) n0
           end t0).

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__helper2 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__cond y -> choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__helper3 :  forall (y : NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type), NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F2 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__helper4 : (forall b : choice NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list, choice_cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list b -> NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__cond (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F2 b) /\ NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F1 (NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F2.
Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__cond :=
  (* Eval compute in *) proj2_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__list__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F1 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__F2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__helper2 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__helper3 NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__helper4.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__cond := empty_format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__Format.

Definition NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__Format : T_Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__Type NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__cond := sum_format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__root__Format NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__ext__Format.
Opaque NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__cond NR_DL_PRS_Periodicity_and_ResourceSetSlotOffset_r17__Format.

