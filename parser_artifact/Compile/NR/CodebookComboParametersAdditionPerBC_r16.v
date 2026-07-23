Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__cond z) .

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__helper1 : (0 <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z. unfold maxNrofCSI_RS_ResourcesAlt_1_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesAlt_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__Type := Z.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__cond := (fun z => (0 <= z <= maxNrofCSI_RS_ResourcesAlt_1_r16)%Z).
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__Type := list Z.

Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__helper1 : (0 <= 1 <= maxNrofCSI_RS_ResourcesExt_r16)%Z. unfold maxNrofCSI_RS_ResourcesExt_r16.
 lia. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesExt_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesExt_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__cond (z : CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_ResourcesExt_r16)%Z /\ (list_and CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__cond z) .

Record CodebookComboParametersAdditionPerBC_r16__Type : Set :=
  make__CodebookComboParametersAdditionPerBC_r16__Type {
    CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16 : option CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16 : option CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__Type ;
    CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16 : option CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__Type ;
}.
Definition CodebookComboParametersAdditionPerBC_r16__list := (
 Opt CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__cond ::
 nil).
Definition CodebookComboParametersAdditionPerBC_r16__cond z := 
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__cond (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16 z) /\
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
Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__Type CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__cond CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__cond CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__Format : T_Format Z CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__cond :=
 ranged_int_format (0) (maxNrofCSI_RS_ResourcesAlt_1_r16) CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__Format.

Definition CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__Type CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__cond := seq_of_format CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__seq_of__Format 1 maxNrofCSI_RS_ResourcesExt_r16 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__helper1 CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__helper2.

Opaque CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__cond CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__Format.


Definition CodebookComboParametersAdditionPerBC_r16__Format_Type := Eval cbn in seq_format_prod CodebookComboParametersAdditionPerBC_r16__list.
Definition CodebookComboParametersAdditionPerBC_r16__Format_list : CodebookComboParametersAdditionPerBC_r16__Format_Type :=
  (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16__Format, (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16__Format, unit_format)))))))))))))).
Definition CodebookComboParametersAdditionPerBC_r16__list__Format := (*Eval compute in *) seq_format CodebookComboParametersAdditionPerBC_r16__list CodebookComboParametersAdditionPerBC_r16__Format_list.
Definition CodebookComboParametersAdditionPerBC_r16__F1 z :=
  (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2PS_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R1PS_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1SP_eType2R2PS_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1SP_Type2_Type2PS_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2PS_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R1PS_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1MP_eType2R2PS_null_r16 z, (CodebookComboParametersAdditionPerBC_r16__type1MP_Type2_Type2PS_r16 z, tt)))))))))))))).
Definition CodebookComboParametersAdditionPerBC_r16__F2 (y : seq_type CodebookComboParametersAdditionPerBC_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, _))))))))))))))=>
    make__CodebookComboParametersAdditionPerBC_r16__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  end.
Lemma CodebookComboParametersAdditionPerBC_r16__F1F2_cond (z : CodebookComboParametersAdditionPerBC_r16__Type)
  : CodebookComboParametersAdditionPerBC_r16__cond z ->
  (seq_cond CodebookComboParametersAdditionPerBC_r16__list (CodebookComboParametersAdditionPerBC_r16__F1 z)).
intro H. unfold CodebookComboParametersAdditionPerBC_r16__cond in H. simpl. auto. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__F1F2_cond2 (z : CodebookComboParametersAdditionPerBC_r16__Type)
 : CodebookComboParametersAdditionPerBC_r16__F2 (CodebookComboParametersAdditionPerBC_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CodebookComboParametersAdditionPerBC_r16__F2F1_cond (y : seq_type CodebookComboParametersAdditionPerBC_r16__list)
  : seq_cond CodebookComboParametersAdditionPerBC_r16__list y ->
 (CodebookComboParametersAdditionPerBC_r16__cond (CodebookComboParametersAdditionPerBC_r16__F2 y)) /\  CodebookComboParametersAdditionPerBC_r16__F1 (CodebookComboParametersAdditionPerBC_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CodebookComboParametersAdditionPerBC_r16__cond. simpl in *. auto.
 - simpl. unfold CodebookComboParametersAdditionPerBC_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CodebookComboParametersAdditionPerBC_r16__Format : T_Format CodebookComboParametersAdditionPerBC_r16__Type CodebookComboParametersAdditionPerBC_r16__cond :=
        proj2_format  CodebookComboParametersAdditionPerBC_r16__cond CodebookComboParametersAdditionPerBC_r16__list__Format
    CodebookComboParametersAdditionPerBC_r16__F1 CodebookComboParametersAdditionPerBC_r16__F2 CodebookComboParametersAdditionPerBC_r16__F1F2_cond  CodebookComboParametersAdditionPerBC_r16__F1F2_cond2 CodebookComboParametersAdditionPerBC_r16__F2F1_cond.
Opaque CodebookComboParametersAdditionPerBC_r16__cond CodebookComboParametersAdditionPerBC_r16__Format.

