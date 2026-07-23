Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__Type := Z.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__cond := (fun z => (0 <= z <= 4)%Z).
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__Type := Z.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__cond := (fun z => (0 <= z <= 9)%Z).
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__Type := Z.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__cond := (fun z => (0 <= z <= 4)%Z).

Inductive PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type : Set :=
  | PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15 : Z -> PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type
  | PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30 : Z -> PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type
.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list : list typ := (
typ_cons Z PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__cond ::
typ_cons Z PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__cond ::
 nil).
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__cond (c : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type) := 
  match c with
  | PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15 t => PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__cond t 
  | PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30 t => PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__cond t 
  end.

Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__len_helper1 : to_bit_sz (length PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__len_helper2 : 2 <= length2 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list.
 simpl. lia. Qed.
Record PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Type : Set :=
  make__PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Type {
    PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16 : Z ;
    PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16 : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type ;
}.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list := (
 Nor Z PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__cond ::
 Nor PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__cond ::
 nil).
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond z := 
  PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__cond (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16 z) /\
  PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__cond (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16 z) /\
  True.

Lemma PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__Type := Z.
Definition PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__cond := (fun z => (0 <= z <= 9)%Z).
Inductive PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Type : Set :=
 | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__n2
 | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__n4
.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__cond := (fun (_ : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Type) => True).
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__nat__helper.

Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F1 t :=
  match t with
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__n2 => 0
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__n4 => 1
  end.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F2 n :=
  match n with
  | 0 => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__n2
  | 1 => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__n4
  | _ => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__n2
  end.
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F1F2 : forall x : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Type, (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F1 x <= 1) /\ PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F2 (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F2F1 : forall (y : nat) (H : y <= 1), PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F1 (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F2 y) = y. enum_solve H y. Qed.

Inductive PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Type : Set :=
 | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n0
 | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n1
 | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n2
 | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n3
.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__cond := (fun (_ : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Type) => True).
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__nat__helper.

Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F1 t :=
  match t with
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n0 => 0
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n1 => 1
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n2 => 2
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n3 => 3
  end.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F2 n :=
  match n with
  | 0 => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n0
  | 1 => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n1
  | 2 => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n2
  | 3 => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n3
  | _ => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__n0
  end.
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F1F2 : forall x : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Type, (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F1 x <= 3) /\ PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F2 (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F2F1 : forall (y : nat) (H : y <= 3), PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F1 (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F2 y) = y. enum_solve H y. Qed.

Record PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type : Set :=
  make__PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type {
    PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610 : option PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Type ;
    PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610 : option PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Type ;
}.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list := (
 Opt PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Type PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__cond ::
 Opt PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Type PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__cond ::
 nil).
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond z := 
  opt_cond PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__cond (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610 z) /\
  opt_cond PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__cond (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610 z) /\
  True.


Inductive PUCCH_ResourceExt_v1610__format_v1610__Type : Set :=
  | PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610 : Z -> PUCCH_ResourceExt_v1610__format_v1610__Type
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610 : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type -> PUCCH_ResourceExt_v1610__format_v1610__Type
.
Definition PUCCH_ResourceExt_v1610__format_v1610__list : list typ := (
typ_cons Z PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__cond ::
typ_cons PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond ::
 nil).
Definition PUCCH_ResourceExt_v1610__format_v1610__cond (c : PUCCH_ResourceExt_v1610__format_v1610__Type) := 
  match c with
  | PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610 t => PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__cond t 
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610 t => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond t 
  end.

Lemma PUCCH_ResourceExt_v1610__format_v1610__len_helper1 : to_bit_sz (length PUCCH_ResourceExt_v1610__format_v1610__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PUCCH_ResourceExt_v1610__format_v1610__len_helper2 : 2 <= length2 PUCCH_ResourceExt_v1610__format_v1610__list.
 simpl. lia. Qed.
Lemma PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__Type := Z.
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__cond := (fun z => (1 <= z <= 16)%Z).
Record PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Type : Set :=
  make__PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Type {
    PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17 : Z ;
}.
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list := (
 Nor Z PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__cond ::
 nil).
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond z := 
  PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__cond (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17 z) /\
  True.

Inductive PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Type : Set :=
 | PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n1
 | PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n2
 | PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n4
 | PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n8
.
Definition PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__cond := (fun (_ : PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Type) => True).
Lemma PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__nat__helper.

Definition PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F1 t :=
  match t with
  | PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n1 => 0
  | PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n2 => 1
  | PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n4 => 2
  | PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n8 => 3
  end.
Definition PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F2 n :=
  match n with
  | 0 => PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n1
  | 1 => PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n2
  | 2 => PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n4
  | 3 => PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n8
  | _ => PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__n1
  end.
Lemma PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F1F2 : forall x : PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Type, (PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F1 x <= 3) /\ PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F2 (PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F2F1 : forall (y : nat) (H : y <= 3), PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F1 (PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F2 y) = y. enum_solve H y. Qed.

Record PUCCH_ResourceExt_v1610__ext0O__Type : Set :=
  make__PUCCH_ResourceExt_v1610__ext0O__Type {
    PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700 : option PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Type ;
    PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17 : option PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Type ;
}.
Definition PUCCH_ResourceExt_v1610__ext0O__list := (
 Opt PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Type PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond ::
 Opt PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Type PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__cond ::
 nil).
Definition PUCCH_ResourceExt_v1610__ext0O__cond z := 
  opt_cond PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700 z) /\
  opt_cond PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__cond (PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17 z) /\
  True.

Definition PUCCH_ResourceExt_v1610__ext0__Type := PUCCH_ResourceExt_v1610__ext0O__Type.
Definition PUCCH_ResourceExt_v1610__ext0__cond := PUCCH_ResourceExt_v1610__ext0O__cond.

Record PUCCH_ResourceExt_v1610__Type : Set :=
  make__PUCCH_ResourceExt_v1610__Type {
    PUCCH_ResourceExt_v1610__interlaceAllocation_r16 : option PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Type ;
    PUCCH_ResourceExt_v1610__format_v1610 : option PUCCH_ResourceExt_v1610__format_v1610__Type ;
    PUCCH_ResourceExt_v1610__ext0 : option PUCCH_ResourceExt_v1610__ext0__Type ;
}.
Definition PUCCH_ResourceExt_v1610__root_list : list seq_elem := (
 Opt PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Type PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond ::
 Opt PUCCH_ResourceExt_v1610__format_v1610__Type PUCCH_ResourceExt_v1610__format_v1610__cond ::
 nil).
Definition PUCCH_ResourceExt_v1610__ext_list : list typ := (
  typ_cons PUCCH_ResourceExt_v1610__ext0__Type PUCCH_ResourceExt_v1610__ext0__cond ::
  nil).
Definition PUCCH_ResourceExt_v1610__cond (z : PUCCH_ResourceExt_v1610__Type) := 
(  opt_cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond (PUCCH_ResourceExt_v1610__interlaceAllocation_r16 z) /\
  opt_cond PUCCH_ResourceExt_v1610__format_v1610__cond (PUCCH_ResourceExt_v1610__format_v1610 z) /\
  True) /\ 
(  opt_cond PUCCH_ResourceExt_v1610__ext0__cond (PUCCH_ResourceExt_v1610__ext0 z) /\
  True).


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
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__Format : T_Format Z PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__cond :=
 ranged_int_format (0) (4) PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__helper1 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__helper2.

Opaque PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__Format.

Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__Format : T_Format Z PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__cond :=
 ranged_int_format (0) (9) PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__helper1 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__helper2.

Opaque PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__Format.

Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__Format : T_Format Z PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__cond :=
 ranged_int_format (0) (4) PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__helper1 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__helper2.

Opaque PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__Format.


Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Format_Type := Eval cbn in get_formats PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Format_list : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Format_Type :=
  (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15__Format, (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30__Format, unit__Format)).
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list__Format := Eval compute in choice_format PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__len_helper1 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__len_helper2  PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Format_list.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F1 (z : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type) : (choice PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list) :=
  match z with
   | PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15 t => existT _ 0 t
  | PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30 t => existT _ 1 t
  end.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__g := (fun n => typ_set (get_nth_typ PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list n)).
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F2 (y : choice PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list) : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__g n -> PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type) with
    | 0 => fun (t : Z) => PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs15 t 
    | 1 => fun (t : Z) => PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__scs30 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type with end) n0
           end t0).

Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__helper2 :  forall (y : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type), PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__cond y -> choice_cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__helper3 :  forall (y : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type), PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F2 (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__helper4 : (forall b : choice PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list, choice_cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list b -> PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__cond (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F2 b) /\ PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F1 (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F1 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F2.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Format : T_Format PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Type PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__cond :=
  (* Eval compute in *) proj2_format PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__list__Format PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F1 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__F2 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__helper2 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__helper3 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__helper4.
Opaque PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Format.


Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Format_Type := Eval cbn in seq_format_prod PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Format_list : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Format_Type :=
  (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16__Format, (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16__Format, unit_format)).
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list__Format := (*Eval compute in *) seq_format PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Format_list.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1 z :=
  (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__rb_SetIndex_r16 z, (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__interlace0_r16 z, tt)).
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F2 (y : seq_type PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Type i0 i1
  end.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1F2_cond (z : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Type)
  : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond z ->
  (seq_cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1 z)).
intro H. unfold PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond in H. simpl. auto. Qed.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1F2_cond2 (z : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Type)
 : PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F2 (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F2F1_cond (y : seq_type PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list)
  : seq_cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list y ->
 (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F2 y)) /\  PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1 (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond. simpl in *. auto.
 - simpl. unfold PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Format : T_Format PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Type PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond :=
        proj2_format  PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__list__Format
    PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F2 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1F2_cond  PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F1F2_cond2 PUCCH_ResourceExt_v1610__interlaceAllocation_r16__F2F1_cond.
Opaque PUCCH_ResourceExt_v1610__interlaceAllocation_r16__cond PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Format.

Definition PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__Format : T_Format Z PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__cond :=
 ranged_int_format (0) (9) PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__helper1 PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__helper2.

Opaque PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__cond PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__Format.

Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Format : T_Format PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__nat__Format PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F1 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F2 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F1F2 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__F2F1.

Opaque PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__cond PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Format.

Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Format : T_Format PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__nat__Format PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F1 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F2 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F1F2 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__F2F1.

Opaque PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__cond PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Format.


Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Format_Type := Eval cbn in seq_format_prod PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Format_list : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Format_Type :=
  (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610__Format, (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610__Format, unit_format)).
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list__Format := (*Eval compute in *) seq_format PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Format_list.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1 z :=
  (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Length_v1610 z, (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__occ_Index_v1610 z, tt)).
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F2 (y : seq_type PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type i0 i1
  end.
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1F2_cond (z : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type)
  : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond z ->
  (seq_cond PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1 z)).
intro H. unfold PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond in H. simpl. auto. Qed.
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1F2_cond2 (z : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type)
 : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F2 (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F2F1_cond (y : seq_type PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list)
  : seq_cond PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list y ->
 (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F2 y)) /\  PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1 (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond. simpl in *. auto.
 - simpl. unfold PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Format : T_Format PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond :=
        proj2_format  PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__list__Format
    PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F2 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1F2_cond  PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F1F2_cond2 PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__F2F1_cond.
Opaque PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__cond PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Format.


Definition PUCCH_ResourceExt_v1610__format_v1610__Format_Type := Eval cbn in get_formats PUCCH_ResourceExt_v1610__format_v1610__list.
Definition PUCCH_ResourceExt_v1610__format_v1610__Format_list : PUCCH_ResourceExt_v1610__format_v1610__Format_Type :=
  (PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610__Format, (PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Format, unit__Format)).
Definition PUCCH_ResourceExt_v1610__format_v1610__list__Format := Eval compute in choice_format PUCCH_ResourceExt_v1610__format_v1610__list PUCCH_ResourceExt_v1610__format_v1610__len_helper1 PUCCH_ResourceExt_v1610__format_v1610__len_helper2  PUCCH_ResourceExt_v1610__format_v1610__Format_list.
Definition PUCCH_ResourceExt_v1610__format_v1610__F1 (z : PUCCH_ResourceExt_v1610__format_v1610__Type) : (choice PUCCH_ResourceExt_v1610__format_v1610__list) :=
  match z with
   | PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610 t => existT _ 0 t
  | PUCCH_ResourceExt_v1610__format_v1610__occ_v1610 t => existT _ 1 t
  end.
Definition PUCCH_ResourceExt_v1610__format_v1610__g := (fun n => typ_set (get_nth_typ PUCCH_ResourceExt_v1610__format_v1610__list n)).
Definition PUCCH_ResourceExt_v1610__format_v1610__F2 (y : choice PUCCH_ResourceExt_v1610__format_v1610__list) : PUCCH_ResourceExt_v1610__format_v1610__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PUCCH_ResourceExt_v1610__format_v1610__g n -> PUCCH_ResourceExt_v1610__format_v1610__Type) with
    | 0 => fun (t : Z) => PUCCH_ResourceExt_v1610__format_v1610__interlace1_v1610 t 
    | 1 => fun (t : PUCCH_ResourceExt_v1610__format_v1610__occ_v1610__Type) => PUCCH_ResourceExt_v1610__format_v1610__occ_v1610 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PUCCH_ResourceExt_v1610__format_v1610__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PUCCH_ResourceExt_v1610__format_v1610__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PUCCH_ResourceExt_v1610__format_v1610__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PUCCH_ResourceExt_v1610__format_v1610__Type with end) n0
           end t0).

Lemma PUCCH_ResourceExt_v1610__format_v1610__helper2 :  forall (y : PUCCH_ResourceExt_v1610__format_v1610__Type), PUCCH_ResourceExt_v1610__format_v1610__cond y -> choice_cond PUCCH_ResourceExt_v1610__format_v1610__list (PUCCH_ResourceExt_v1610__format_v1610__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PUCCH_ResourceExt_v1610__format_v1610__helper3 :  forall (y : PUCCH_ResourceExt_v1610__format_v1610__Type), PUCCH_ResourceExt_v1610__format_v1610__F2 (PUCCH_ResourceExt_v1610__format_v1610__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PUCCH_ResourceExt_v1610__format_v1610__helper4 : (forall b : choice PUCCH_ResourceExt_v1610__format_v1610__list, choice_cond PUCCH_ResourceExt_v1610__format_v1610__list b -> PUCCH_ResourceExt_v1610__format_v1610__cond (PUCCH_ResourceExt_v1610__format_v1610__F2 b) /\ PUCCH_ResourceExt_v1610__format_v1610__F1 (PUCCH_ResourceExt_v1610__format_v1610__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PUCCH_ResourceExt_v1610__format_v1610__F1 PUCCH_ResourceExt_v1610__format_v1610__F2.
Definition PUCCH_ResourceExt_v1610__format_v1610__Format : T_Format PUCCH_ResourceExt_v1610__format_v1610__Type PUCCH_ResourceExt_v1610__format_v1610__cond :=
  (* Eval compute in *) proj2_format PUCCH_ResourceExt_v1610__format_v1610__cond PUCCH_ResourceExt_v1610__format_v1610__list__Format PUCCH_ResourceExt_v1610__format_v1610__F1 PUCCH_ResourceExt_v1610__format_v1610__F2 PUCCH_ResourceExt_v1610__format_v1610__helper2 PUCCH_ResourceExt_v1610__format_v1610__helper3 PUCCH_ResourceExt_v1610__format_v1610__helper4.
Opaque PUCCH_ResourceExt_v1610__format_v1610__cond PUCCH_ResourceExt_v1610__format_v1610__Format.

Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__Format : T_Format Z PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__cond :=
 ranged_int_format (1) (16) PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__helper1 PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__helper2.

Opaque PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__cond PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__Format.


Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Format_Type := Eval cbn in seq_format_prod PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list.
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Format_list : PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Format_Type :=
  (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17__Format, unit_format).
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list__Format := (*Eval compute in *) seq_format PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Format_list.
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1 z :=
  (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__nrofPRBs_r17 z, tt).
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F2 (y : seq_type PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list) :=
  match y with
  | (i0, _)=>
    make__PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Type i0
  end.
Lemma PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1F2_cond (z : PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Type)
  : PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond z ->
  (seq_cond PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1 z)).
intro H. unfold PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond in H. simpl. auto. Qed.
Lemma PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1F2_cond2 (z : PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Type)
 : PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F2 (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F2F1_cond (y : seq_type PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list)
  : seq_cond PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list y ->
 (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F2 y)) /\  PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1 (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond. simpl in *. auto.
 - simpl. unfold PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Format : T_Format PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Type PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond :=
        proj2_format  PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__list__Format
    PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1 PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F2 PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1F2_cond  PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F1F2_cond2 PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__F2F1_cond.
Opaque PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__cond PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Format.

Definition PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Format : T_Format PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__nat__Format PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F1 PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F2 PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F1F2 PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__F2F1.

Opaque PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__cond PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Format.


Definition PUCCH_ResourceExt_v1610__ext0O__Format_Type := Eval cbn in seq_format_prod PUCCH_ResourceExt_v1610__ext0O__list.
Definition PUCCH_ResourceExt_v1610__ext0O__Format_list : PUCCH_ResourceExt_v1610__ext0O__Format_Type :=
  (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700__Format, (PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17__Format, unit_format)).
Definition PUCCH_ResourceExt_v1610__ext0O__list__Format := (*Eval compute in *) seq_format PUCCH_ResourceExt_v1610__ext0O__list PUCCH_ResourceExt_v1610__ext0O__Format_list.
Definition PUCCH_ResourceExt_v1610__ext0O__F1 z :=
  (PUCCH_ResourceExt_v1610__ext0O__formatExt_v1700 z, (PUCCH_ResourceExt_v1610__ext0O__pucch_RepetitionNrofSlots_r17 z, tt)).
Definition PUCCH_ResourceExt_v1610__ext0O__F2 (y : seq_type PUCCH_ResourceExt_v1610__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUCCH_ResourceExt_v1610__ext0O__Type i0 i1
  end.
Lemma PUCCH_ResourceExt_v1610__ext0O__F1F2_cond (z : PUCCH_ResourceExt_v1610__ext0O__Type)
  : PUCCH_ResourceExt_v1610__ext0O__cond z ->
  (seq_cond PUCCH_ResourceExt_v1610__ext0O__list (PUCCH_ResourceExt_v1610__ext0O__F1 z)).
intro H. unfold PUCCH_ResourceExt_v1610__ext0O__cond in H. simpl. auto. Qed.
Lemma PUCCH_ResourceExt_v1610__ext0O__F1F2_cond2 (z : PUCCH_ResourceExt_v1610__ext0O__Type)
 : PUCCH_ResourceExt_v1610__ext0O__F2 (PUCCH_ResourceExt_v1610__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_ResourceExt_v1610__ext0O__F2F1_cond (y : seq_type PUCCH_ResourceExt_v1610__ext0O__list)
  : seq_cond PUCCH_ResourceExt_v1610__ext0O__list y ->
 (PUCCH_ResourceExt_v1610__ext0O__cond (PUCCH_ResourceExt_v1610__ext0O__F2 y)) /\  PUCCH_ResourceExt_v1610__ext0O__F1 (PUCCH_ResourceExt_v1610__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_ResourceExt_v1610__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUCCH_ResourceExt_v1610__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_ResourceExt_v1610__ext0O__Format : T_Format PUCCH_ResourceExt_v1610__ext0O__Type PUCCH_ResourceExt_v1610__ext0O__cond :=
        proj2_format  PUCCH_ResourceExt_v1610__ext0O__cond PUCCH_ResourceExt_v1610__ext0O__list__Format
    PUCCH_ResourceExt_v1610__ext0O__F1 PUCCH_ResourceExt_v1610__ext0O__F2 PUCCH_ResourceExt_v1610__ext0O__F1F2_cond  PUCCH_ResourceExt_v1610__ext0O__F1F2_cond2 PUCCH_ResourceExt_v1610__ext0O__F2F1_cond.
Opaque PUCCH_ResourceExt_v1610__ext0O__cond PUCCH_ResourceExt_v1610__ext0O__Format.

Definition PUCCH_ResourceExt_v1610__ext0__check_all_none (b : PUCCH_ResourceExt_v1610__ext0O__Type) : bool :=
match b with 
  | make__PUCCH_ResourceExt_v1610__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition PUCCH_ResourceExt_v1610__ext0__Format : T_Format PUCCH_ResourceExt_v1610__ext0__Type PUCCH_ResourceExt_v1610__ext0__cond :=
  restrict_add_format PUCCH_ResourceExt_v1610__ext0__check_all_none PUCCH_ResourceExt_v1610__ext0O__Format.

Opaque PUCCH_ResourceExt_v1610__ext0__cond PUCCH_ResourceExt_v1610__ext0__Format.


Definition PUCCH_ResourceExt_v1610__root_Format_Type := Eval cbn in seq_format_prod PUCCH_ResourceExt_v1610__root_list.
Definition PUCCH_ResourceExt_v1610__root_Format_list : PUCCH_ResourceExt_v1610__root_Format_Type :=
  (PUCCH_ResourceExt_v1610__interlaceAllocation_r16__Format, (PUCCH_ResourceExt_v1610__format_v1610__Format, unit_format)).

Definition PUCCH_ResourceExt_v1610__ext_Format_Type := Eval cbn in get_formats PUCCH_ResourceExt_v1610__ext_list.
Definition PUCCH_ResourceExt_v1610__ext_Format_list : PUCCH_ResourceExt_v1610__ext_Format_Type :=
  (PUCCH_ResourceExt_v1610__ext0__Format, unit__Format).

Definition PUCCH_ResourceExt_v1610__list_type : Set := (seq_type PUCCH_ResourceExt_v1610__root_list) * (seq_ext_type PUCCH_ResourceExt_v1610__ext_list).
Definition PUCCH_ResourceExt_v1610__list_cond (z : PUCCH_ResourceExt_v1610__list_type) : Prop :=
        (seq_cond PUCCH_ResourceExt_v1610__root_list (fst z)) /\ (seq_ext_cond PUCCH_ResourceExt_v1610__ext_list (snd z)).
Definition PUCCH_ResourceExt_v1610__list_format : T_Format PUCCH_ResourceExt_v1610__list_type PUCCH_ResourceExt_v1610__list_cond :=
 (* Eval compute in *) seq_ext_format PUCCH_ResourceExt_v1610__root_list PUCCH_ResourceExt_v1610__root_Format_list PUCCH_ResourceExt_v1610__ext_list PUCCH_ResourceExt_v1610__ext_Format_list.

Opaque PUCCH_ResourceExt_v1610__list_format.
Definition PUCCH_ResourceExt_v1610__F1 (z : PUCCH_ResourceExt_v1610__Type) : PUCCH_ResourceExt_v1610__list_type :=
  (((PUCCH_ResourceExt_v1610__interlaceAllocation_r16 z, (PUCCH_ResourceExt_v1610__format_v1610 z, tt))), (
(PUCCH_ResourceExt_v1610__ext0 z, tt))).
Definition PUCCH_ResourceExt_v1610__F2 (y : PUCCH_ResourceExt_v1610__list_type) : PUCCH_ResourceExt_v1610__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__PUCCH_ResourceExt_v1610__Type j0 j1 i0
  end.
Definition PUCCH_ResourceExt_v1610__helper1 : (forall a : PUCCH_ResourceExt_v1610__Type, PUCCH_ResourceExt_v1610__cond a -> PUCCH_ResourceExt_v1610__list_cond (PUCCH_ResourceExt_v1610__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUCCH_ResourceExt_v1610__helper2 : (forall a : PUCCH_ResourceExt_v1610__Type, PUCCH_ResourceExt_v1610__F2 (PUCCH_ResourceExt_v1610__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUCCH_ResourceExt_v1610__helper3 : (forall b : PUCCH_ResourceExt_v1610__list_type, PUCCH_ResourceExt_v1610__list_cond b -> PUCCH_ResourceExt_v1610__cond (PUCCH_ResourceExt_v1610__F2 b) /\ PUCCH_ResourceExt_v1610__F1 (PUCCH_ResourceExt_v1610__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUCCH_ResourceExt_v1610__cond, PUCCH_ResourceExt_v1610__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUCCH_ResourceExt_v1610__Format : T_Format PUCCH_ResourceExt_v1610__Type PUCCH_ResourceExt_v1610__cond :=
 proj2_format PUCCH_ResourceExt_v1610__cond PUCCH_ResourceExt_v1610__list_format  PUCCH_ResourceExt_v1610__F1 PUCCH_ResourceExt_v1610__F2 PUCCH_ResourceExt_v1610__helper1 PUCCH_ResourceExt_v1610__helper2 PUCCH_ResourceExt_v1610__helper3.

Opaque PUCCH_ResourceExt_v1610__cond PUCCH_ResourceExt_v1610__Format.

