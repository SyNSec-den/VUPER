Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_null_null__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_null_null__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_null_null__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_null_null__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_null_null__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_null_null__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__cond z) .

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__Type := Z.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__Type := list Z.

Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__cond (z : CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__cond z) .

Record CodebookComboParameterMultiTRP_r17__Type : Set :=
  make__CodebookComboParameterMultiTRP_r17__Type {
    CodebookComboParameterMultiTRP_r17__nCJT_null_null : option CodebookComboParameterMultiTRP_r17__nCJT_null_null__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null : option CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16 : option CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17 : option CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17 : option CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17 : option CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17 : option CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17 : option CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17 : option CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17 : option CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__Type ;
    CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17 : option CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__Type ;
}.
Definition CodebookComboParameterMultiTRP_r17__list := (
 Opt CodebookComboParameterMultiTRP_r17__nCJT_null_null__Type CodebookComboParameterMultiTRP_r17__nCJT_null_null__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__cond ::
 nil).
Definition CodebookComboParameterMultiTRP_r17__cond z := 
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_null_null__cond (CodebookComboParameterMultiTRP_r17__nCJT_null_null z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__cond (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17 z) /\
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
Definition CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_null_null__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_null_null__Type CodebookComboParameterMultiTRP_r17__nCJT_null_null__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_null_null__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_null_null__helper1 CodebookComboParameterMultiTRP_r17__nCJT_null_null__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_null_null__cond CodebookComboParameterMultiTRP_r17__nCJT_null_null__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__cond CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__cond CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__cond CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__Format : T_Format Z CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__Format.

Definition CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__Type CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__cond := seq_of_format CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__helper1 CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__helper2.

Opaque CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__cond CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__Format.


Definition CodebookComboParameterMultiTRP_r17__Format_Type := Eval cbn in seq_format_prod CodebookComboParameterMultiTRP_r17__list.
Definition CodebookComboParameterMultiTRP_r17__Format_list : CodebookComboParameterMultiTRP_r17__Format_Type :=
  (CodebookComboParameterMultiTRP_r17__nCJT_null_null__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null__Format, (CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16__Format, (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17__Format, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17__Format, unit_format)))))))))))))))))))))))))))))).
Definition CodebookComboParameterMultiTRP_r17__list__Format := (*Eval compute in *) seq_format CodebookComboParameterMultiTRP_r17__list CodebookComboParameterMultiTRP_r17__Format_list.
Definition CodebookComboParameterMultiTRP_r17__F1 z :=
  (CodebookComboParameterMultiTRP_r17__nCJT_null_null z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_null_null z, (CodebookComboParameterMultiTRP_r17__nCJT_Type2_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT_Type2PS_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R2_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1PS_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R2PS_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT_Type2_Type2PS_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2PS_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1PS_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R2PS_null_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_Type2PS_r16 z, (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_null_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R1_null_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT_feType2PS_M2R2_null_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M1_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT_Type2_feType2_PS_M2R1_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M1_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT_eType2R1_feType2_PS_M2R1_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_null_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R1_null_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_feType2PS_M2R2_null_r1 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M1_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_Type2_feType2_PS_M2R1_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M1_r17 z, (CodebookComboParameterMultiTRP_r17__nCJT1SP_eType2R1_feType2_PS_M2R1_r17 z, tt)))))))))))))))))))))))))))))).
Definition CodebookComboParameterMultiTRP_r17__F2 (y : seq_type CodebookComboParameterMultiTRP_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, (i24, (i25, (i26, (i27, (i28, (i29, _))))))))))))))))))))))))))))))=>
    make__CodebookComboParameterMultiTRP_r17__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29
  end.
Lemma CodebookComboParameterMultiTRP_r17__F1F2_cond (z : CodebookComboParameterMultiTRP_r17__Type)
  : CodebookComboParameterMultiTRP_r17__cond z ->
  (seq_cond CodebookComboParameterMultiTRP_r17__list (CodebookComboParameterMultiTRP_r17__F1 z)).
intro H. unfold CodebookComboParameterMultiTRP_r17__cond in H. simpl. auto. Qed.
Lemma CodebookComboParameterMultiTRP_r17__F1F2_cond2 (z : CodebookComboParameterMultiTRP_r17__Type)
 : CodebookComboParameterMultiTRP_r17__F2 (CodebookComboParameterMultiTRP_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookComboParameterMultiTRP_r17__F2F1_cond (y : seq_type CodebookComboParameterMultiTRP_r17__list)
  : seq_cond CodebookComboParameterMultiTRP_r17__list y ->
 (CodebookComboParameterMultiTRP_r17__cond (CodebookComboParameterMultiTRP_r17__F2 y)) /\  CodebookComboParameterMultiTRP_r17__F1 (CodebookComboParameterMultiTRP_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookComboParameterMultiTRP_r17__cond. simpl in *. auto.
 - simpl. unfold CodebookComboParameterMultiTRP_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookComboParameterMultiTRP_r17__Format : T_Format CodebookComboParameterMultiTRP_r17__Type CodebookComboParameterMultiTRP_r17__cond :=
        proj2_format  CodebookComboParameterMultiTRP_r17__cond CodebookComboParameterMultiTRP_r17__list__Format
    CodebookComboParameterMultiTRP_r17__F1 CodebookComboParameterMultiTRP_r17__F2 CodebookComboParameterMultiTRP_r17__F1F2_cond  CodebookComboParameterMultiTRP_r17__F1F2_cond2 CodebookComboParameterMultiTRP_r17__F2F1_cond.
Opaque CodebookComboParameterMultiTRP_r17__cond CodebookComboParameterMultiTRP_r17__Format.

