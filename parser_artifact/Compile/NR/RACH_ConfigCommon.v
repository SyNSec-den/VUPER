Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RACH_ConfigGeneric.

Opaque RACH_ConfigGeneric__cond RACH_ConfigGeneric__Format.

Lemma RACH_ConfigCommon__totalNumberOfRA_Preambles__helper1 : (1 <= 63)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__totalNumberOfRA_Preambles__helper2 : to_bit_sz (Z.to_nat (63 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__totalNumberOfRA_Preambles__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__totalNumberOfRA_Preambles__Type := Z.
Definition RACH_ConfigCommon__totalNumberOfRA_Preambles__cond := (fun z => (1 <= z <= 63)%Z).
Inductive RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Type : Set :=
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n4
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n8
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n12
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n16
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n20
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n24
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n28
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n32
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n36
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n40
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n44
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n48
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n52
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n56
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n60
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n64
.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__cond := (fun (_ : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Type) => True).
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__nat__helper.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F1 t :=
  match t with
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n4 => 0
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n8 => 1
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n12 => 2
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n16 => 3
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n20 => 4
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n24 => 5
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n28 => 6
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n32 => 7
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n36 => 8
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n40 => 9
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n44 => 10
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n48 => 11
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n52 => 12
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n56 => 13
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n60 => 14
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n64 => 15
  end.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n4
  | 1 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n8
  | 2 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n12
  | 3 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n16
  | 4 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n20
  | 5 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n24
  | 6 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n28
  | 7 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n32
  | 8 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n36
  | 9 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n40
  | 10 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n44
  | 11 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n48
  | 12 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n52
  | 13 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n56
  | 14 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n60
  | 15 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n64
  | _ => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__n4
  end.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F1F2 : forall x : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Type, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F1 x <= 15) /\ RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F2 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F2F1 : forall (y : nat) (H : y <= 15), RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F1 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Type : Set :=
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n4
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n8
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n12
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n16
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n20
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n24
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n28
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n32
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n36
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n40
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n44
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n48
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n52
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n56
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n60
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n64
.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__cond := (fun (_ : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Type) => True).
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__nat__helper.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F1 t :=
  match t with
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n4 => 0
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n8 => 1
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n12 => 2
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n16 => 3
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n20 => 4
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n24 => 5
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n28 => 6
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n32 => 7
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n36 => 8
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n40 => 9
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n44 => 10
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n48 => 11
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n52 => 12
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n56 => 13
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n60 => 14
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n64 => 15
  end.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n4
  | 1 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n8
  | 2 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n12
  | 3 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n16
  | 4 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n20
  | 5 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n24
  | 6 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n28
  | 7 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n32
  | 8 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n36
  | 9 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n40
  | 10 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n44
  | 11 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n48
  | 12 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n52
  | 13 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n56
  | 14 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n60
  | 15 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n64
  | _ => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__n4
  end.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F1F2 : forall x : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Type, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F1 x <= 15) /\ RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F2 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F2F1 : forall (y : nat) (H : y <= 15), RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F1 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Type : Set :=
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n4
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n8
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n12
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n16
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n20
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n24
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n28
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n32
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n36
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n40
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n44
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n48
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n52
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n56
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n60
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n64
.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__cond := (fun (_ : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Type) => True).
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__nat__helper.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F1 t :=
  match t with
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n4 => 0
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n8 => 1
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n12 => 2
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n16 => 3
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n20 => 4
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n24 => 5
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n28 => 6
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n32 => 7
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n36 => 8
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n40 => 9
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n44 => 10
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n48 => 11
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n52 => 12
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n56 => 13
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n60 => 14
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n64 => 15
  end.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n4
  | 1 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n8
  | 2 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n12
  | 3 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n16
  | 4 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n20
  | 5 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n24
  | 6 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n28
  | 7 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n32
  | 8 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n36
  | 9 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n40
  | 10 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n44
  | 11 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n48
  | 12 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n52
  | 13 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n56
  | 14 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n60
  | 15 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n64
  | _ => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__n4
  end.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F1F2 : forall x : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Type, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F1 x <= 15) /\ RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F2 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F2F1 : forall (y : nat) (H : y <= 15), RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F1 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Type : Set :=
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n4
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n8
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n12
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n16
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n20
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n24
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n28
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n32
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n36
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n40
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n44
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n48
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n52
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n56
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n60
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n64
.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__cond := (fun (_ : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Type) => True).
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__nat__helper.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F1 t :=
  match t with
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n4 => 0
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n8 => 1
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n12 => 2
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n16 => 3
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n20 => 4
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n24 => 5
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n28 => 6
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n32 => 7
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n36 => 8
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n40 => 9
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n44 => 10
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n48 => 11
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n52 => 12
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n56 => 13
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n60 => 14
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n64 => 15
  end.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n4
  | 1 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n8
  | 2 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n12
  | 3 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n16
  | 4 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n20
  | 5 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n24
  | 6 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n28
  | 7 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n32
  | 8 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n36
  | 9 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n40
  | 10 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n44
  | 11 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n48
  | 12 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n52
  | 13 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n56
  | 14 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n60
  | 15 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n64
  | _ => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__n4
  end.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F1F2 : forall x : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Type, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F1 x <= 15) /\ RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F2 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F2F1 : forall (y : nat) (H : y <= 15), RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F1 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Type : Set :=
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n4
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n8
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n12
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n16
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n20
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n24
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n28
 | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n32
.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__cond := (fun (_ : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Type) => True).
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__nat__helper.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F1 t :=
  match t with
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n4 => 0
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n8 => 1
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n12 => 2
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n16 => 3
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n20 => 4
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n24 => 5
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n28 => 6
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n32 => 7
  end.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n4
  | 1 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n8
  | 2 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n12
  | 3 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n16
  | 4 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n20
  | 5 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n24
  | 6 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n28
  | 7 => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n32
  | _ => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__n4
  end.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F1F2 : forall x : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Type, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F1 x <= 7) /\ RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F2 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F2F1 : forall (y : nat) (H : y <= 7), RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F1 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F2 y) = y. enum_solve H y. Qed.

Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__Type := Z.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__cond := (fun z => (1 <= z <= 16)%Z).
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__Type := Z.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__cond := (fun z => (1 <= z <= 8)%Z).
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__Type := Z.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__cond := (fun z => (1 <= z <= 4)%Z).

Inductive RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type : Set :=
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Type -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Type -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Type -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Type -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Type -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four : Z -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight : Z -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen : Z -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type
.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list : list typ := (
typ_cons RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Type RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__cond ::
typ_cons RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Type RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__cond ::
typ_cons RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Type RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__cond ::
typ_cons RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Type RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__cond ::
typ_cons RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Type RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__cond ::
typ_cons Z RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__cond ::
typ_cons Z RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__cond ::
typ_cons Z RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__cond ::
 nil).
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__cond (c : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type) := 
  match c with
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth t => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__cond t 
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth t => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__cond t 
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf t => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__cond t 
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one t => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__cond t 
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two t => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__cond t 
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four t => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__cond t 
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight t => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__cond t 
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen t => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__cond t 
  end.

Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__len_helper1 : to_bit_sz (length RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__len_helper2 : 2 <= length2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list.
 simpl. lia. Qed.
Inductive RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Type : Set :=
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b56
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b144
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b208
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b256
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b282
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b480
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b640
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b800
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b1000
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b72
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare6
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare5
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare4
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare3
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare2
 | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare1
.
Definition RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__cond := (fun (_ : RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Type) => True).
Lemma RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__nat__helper.

Definition RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F1 t :=
  match t with
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b56 => 0
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b144 => 1
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b208 => 2
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b256 => 3
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b282 => 4
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b480 => 5
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b640 => 6
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b800 => 7
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b1000 => 8
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b72 => 9
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare6 => 10
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare5 => 11
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare4 => 12
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare3 => 13
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare2 => 14
  | RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare1 => 15
  end.
Definition RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b56
  | 1 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b144
  | 2 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b208
  | 3 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b256
  | 4 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b282
  | 5 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b480
  | 6 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b640
  | 7 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b800
  | 8 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b1000
  | 9 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b72
  | 10 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare6
  | 11 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare5
  | 12 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare4
  | 13 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare3
  | 14 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare2
  | 15 => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__spare1
  | _ => RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__b56
  end.
Lemma RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F1F2 : forall x : RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Type, (RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F1 x <= 15) /\ RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F2 (RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F2F1 : forall (y : nat) (H : y <= 15), RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F1 (RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Type : Set :=
 | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__minusinfinity
 | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB0
 | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB5
 | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB8
 | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB10
 | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB12
 | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB15
 | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB18
.
Definition RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__cond := (fun (_ : RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Type) => True).
Lemma RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__nat__helper.

Definition RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F1 t :=
  match t with
  | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__minusinfinity => 0
  | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB0 => 1
  | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB5 => 2
  | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB8 => 3
  | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB10 => 4
  | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB12 => 5
  | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB15 => 6
  | RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB18 => 7
  end.
Definition RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__minusinfinity
  | 1 => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB0
  | 2 => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB5
  | 3 => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB8
  | 4 => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB10
  | 5 => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB12
  | 6 => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB15
  | 7 => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__dB18
  | _ => RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__minusinfinity
  end.
Lemma RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F1F2 : forall x : RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Type, (RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F1 x <= 7) /\ RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F2 (RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F2F1 : forall (y : nat) (H : y <= 7), RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F1 (RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F2 y) = y. enum_solve H y. Qed.

Lemma RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__Type := Z.
Definition RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__cond := (fun z => (1 <= z <= 64)%Z).
Record RACH_ConfigCommon__groupBconfigured__Type : Set :=
  make__RACH_ConfigCommon__groupBconfigured__Type {
    RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA : RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Type ;
    RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB : RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Type ;
    RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA : Z ;
}.
Definition RACH_ConfigCommon__groupBconfigured__list := (
 Nor RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Type RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__cond ::
 Nor RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Type RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__cond ::
 Nor Z RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__cond ::
 nil).
Definition RACH_ConfigCommon__groupBconfigured__cond z := 
  RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__cond (RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA z) /\
  RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__cond (RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB z) /\
  RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__cond (RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA z) /\
  True.

Inductive RACH_ConfigCommon__ra_ContentionResolutionTimer__Type : Set :=
 | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf8
 | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf16
 | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf24
 | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf32
 | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf40
 | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf48
 | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf56
 | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf64
.
Definition RACH_ConfigCommon__ra_ContentionResolutionTimer__cond := (fun (_ : RACH_ConfigCommon__ra_ContentionResolutionTimer__Type) => True).
Lemma RACH_ConfigCommon__ra_ContentionResolutionTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__ra_ContentionResolutionTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RACH_ConfigCommon__ra_ContentionResolutionTimer__nat__helper.

Definition RACH_ConfigCommon__ra_ContentionResolutionTimer__F1 t :=
  match t with
  | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf8 => 0
  | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf16 => 1
  | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf24 => 2
  | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf32 => 3
  | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf40 => 4
  | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf48 => 5
  | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf56 => 6
  | RACH_ConfigCommon__ra_ContentionResolutionTimer__sf64 => 7
  end.
Definition RACH_ConfigCommon__ra_ContentionResolutionTimer__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf8
  | 1 => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf16
  | 2 => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf24
  | 3 => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf32
  | 4 => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf40
  | 5 => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf48
  | 6 => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf56
  | 7 => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf64
  | _ => RACH_ConfigCommon__ra_ContentionResolutionTimer__sf8
  end.
Lemma RACH_ConfigCommon__ra_ContentionResolutionTimer__F1F2 : forall x : RACH_ConfigCommon__ra_ContentionResolutionTimer__Type, (RACH_ConfigCommon__ra_ContentionResolutionTimer__F1 x <= 7) /\ RACH_ConfigCommon__ra_ContentionResolutionTimer__F2 (RACH_ConfigCommon__ra_ContentionResolutionTimer__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__ra_ContentionResolutionTimer__F2F1 : forall (y : nat) (H : y <= 7), RACH_ConfigCommon__ra_ContentionResolutionTimer__F1 (RACH_ConfigCommon__ra_ContentionResolutionTimer__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Lemma RACH_ConfigCommon__prach_RootSequenceIndex__l839__helper1 : (0 <= 837)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__prach_RootSequenceIndex__l839__helper2 : to_bit_sz (Z.to_nat (837 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (837 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__prach_RootSequenceIndex__l839__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__l839__Type := Z.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__l839__cond := (fun z => (0 <= z <= 837)%Z).
Lemma RACH_ConfigCommon__prach_RootSequenceIndex__l139__helper1 : (0 <= 137)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__prach_RootSequenceIndex__l139__helper2 : to_bit_sz (Z.to_nat (137 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (137 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__prach_RootSequenceIndex__l139__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__l139__Type := Z.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__l139__cond := (fun z => (0 <= z <= 137)%Z).

Inductive RACH_ConfigCommon__prach_RootSequenceIndex__Type : Set :=
  | RACH_ConfigCommon__prach_RootSequenceIndex__l839 : Z -> RACH_ConfigCommon__prach_RootSequenceIndex__Type
  | RACH_ConfigCommon__prach_RootSequenceIndex__l139 : Z -> RACH_ConfigCommon__prach_RootSequenceIndex__Type
.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__list : list typ := (
typ_cons Z RACH_ConfigCommon__prach_RootSequenceIndex__l839__cond ::
typ_cons Z RACH_ConfigCommon__prach_RootSequenceIndex__l139__cond ::
 nil).
Definition RACH_ConfigCommon__prach_RootSequenceIndex__cond (c : RACH_ConfigCommon__prach_RootSequenceIndex__Type) := 
  match c with
  | RACH_ConfigCommon__prach_RootSequenceIndex__l839 t => RACH_ConfigCommon__prach_RootSequenceIndex__l839__cond t 
  | RACH_ConfigCommon__prach_RootSequenceIndex__l139 t => RACH_ConfigCommon__prach_RootSequenceIndex__l139__cond t 
  end.

Lemma RACH_ConfigCommon__prach_RootSequenceIndex__len_helper1 : to_bit_sz (length RACH_ConfigCommon__prach_RootSequenceIndex__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RACH_ConfigCommon__prach_RootSequenceIndex__len_helper2 : 2 <= length2 RACH_ConfigCommon__prach_RootSequenceIndex__list.
 simpl. lia. Qed.
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Inductive RACH_ConfigCommon__restrictedSetConfig__Type : Set :=
 | RACH_ConfigCommon__restrictedSetConfig__unrestrictedSet
 | RACH_ConfigCommon__restrictedSetConfig__restrictedSetTypeA
 | RACH_ConfigCommon__restrictedSetConfig__restrictedSetTypeB
.
Definition RACH_ConfigCommon__restrictedSetConfig__cond := (fun (_ : RACH_ConfigCommon__restrictedSetConfig__Type) => True).
Lemma RACH_ConfigCommon__restrictedSetConfig__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__restrictedSetConfig__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 RACH_ConfigCommon__restrictedSetConfig__nat__helper.

Definition RACH_ConfigCommon__restrictedSetConfig__F1 t :=
  match t with
  | RACH_ConfigCommon__restrictedSetConfig__unrestrictedSet => 0
  | RACH_ConfigCommon__restrictedSetConfig__restrictedSetTypeA => 1
  | RACH_ConfigCommon__restrictedSetConfig__restrictedSetTypeB => 2
  end.
Definition RACH_ConfigCommon__restrictedSetConfig__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__restrictedSetConfig__unrestrictedSet
  | 1 => RACH_ConfigCommon__restrictedSetConfig__restrictedSetTypeA
  | 2 => RACH_ConfigCommon__restrictedSetConfig__restrictedSetTypeB
  | _ => RACH_ConfigCommon__restrictedSetConfig__unrestrictedSet
  end.
Lemma RACH_ConfigCommon__restrictedSetConfig__F1F2 : forall x : RACH_ConfigCommon__restrictedSetConfig__Type, (RACH_ConfigCommon__restrictedSetConfig__F1 x <= 2) /\ RACH_ConfigCommon__restrictedSetConfig__F2 (RACH_ConfigCommon__restrictedSetConfig__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__restrictedSetConfig__F2F1 : forall (y : nat) (H : y <= 2), RACH_ConfigCommon__restrictedSetConfig__F1 (RACH_ConfigCommon__restrictedSetConfig__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigCommon__msg3_transformPrecoder__Type : Set :=
 | RACH_ConfigCommon__msg3_transformPrecoder__enabled
.
Definition RACH_ConfigCommon__msg3_transformPrecoder__cond := (fun (_ : RACH_ConfigCommon__msg3_transformPrecoder__Type) => True).
Lemma RACH_ConfigCommon__msg3_transformPrecoder__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigCommon__msg3_transformPrecoder__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RACH_ConfigCommon__msg3_transformPrecoder__nat__helper.

Definition RACH_ConfigCommon__msg3_transformPrecoder__F1 t :=
  match t with
  | RACH_ConfigCommon__msg3_transformPrecoder__enabled => 0
  end.
Definition RACH_ConfigCommon__msg3_transformPrecoder__F2 n :=
  match n with
  | 0 => RACH_ConfigCommon__msg3_transformPrecoder__enabled
  | _ => RACH_ConfigCommon__msg3_transformPrecoder__enabled
  end.
Lemma RACH_ConfigCommon__msg3_transformPrecoder__F1F2 : forall x : RACH_ConfigCommon__msg3_transformPrecoder__Type, (RACH_ConfigCommon__msg3_transformPrecoder__F1 x <= 0) /\ RACH_ConfigCommon__msg3_transformPrecoder__F2 (RACH_ConfigCommon__msg3_transformPrecoder__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigCommon__msg3_transformPrecoder__F2F1 : forall (y : nat) (H : y <= 0), RACH_ConfigCommon__msg3_transformPrecoder__F1 (RACH_ConfigCommon__msg3_transformPrecoder__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RA_Prioritization.

Opaque RA_Prioritization__cond RA_Prioritization__Format.

Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__Type := bit_string_fixed.
Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Record RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Type : Set :=
  make__RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Type {
    RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_Prioritization_r16 : RA_Prioritization__Type ;
    RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16 : RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__Type ;
}.
Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list := (
 Nor RA_Prioritization__Type RA_Prioritization__cond ::
 Nor RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__Type RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__cond ::
 nil).
Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond z := 
  RA_Prioritization__cond (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_Prioritization_r16 z) /\
  RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__cond (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16 z) /\
  True.

Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__helper1 : (0 <= 569)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__helper2 : to_bit_sz (Z.to_nat (569 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (569 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__Type := Z.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__cond := (fun z => (0 <= z <= 569)%Z).
Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__helper1 : (0 <= 1149)%Z.  lia. Qed.
Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__helper2 : to_bit_sz (Z.to_nat (1149 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1149 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__Type := Z.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__cond := (fun z => (0 <= z <= 1149)%Z).

Inductive RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type : Set :=
  | RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571 : Z -> RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type
  | RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151 : Z -> RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type
.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list : list typ := (
typ_cons Z RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__cond ::
typ_cons Z RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__cond ::
 nil).
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__cond (c : RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type) := 
  match c with
  | RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571 t => RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__cond t 
  | RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151 t => RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__cond t 
  end.

Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__len_helper1 : to_bit_sz (length RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__len_helper2 : 2 <= length2 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list.
 simpl. lia. Qed.
Record RACH_ConfigCommon__ext0O__Type : Set :=
  make__RACH_ConfigCommon__ext0O__Type {
    RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16 : option RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Type ;
    RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16 : option RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type ;
}.
Definition RACH_ConfigCommon__ext0O__list := (
 Opt RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Type RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond ::
 Opt RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__cond ::
 nil).
Definition RACH_ConfigCommon__ext0O__cond z := 
  opt_cond RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16 z) /\
  opt_cond RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__cond (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16 z) /\
  True.

Definition RACH_ConfigCommon__ext0__Type := RACH_ConfigCommon__ext0O__Type.
Definition RACH_ConfigCommon__ext0__cond := RACH_ConfigCommon__ext0O__cond.

Require Import NR.RA_PrioritizationForSlicing_r17.

Opaque RA_PrioritizationForSlicing_r17__cond RA_PrioritizationForSlicing_r17__Format.

Require Import NR.FeatureCombinationPreambles_r17.

Opaque FeatureCombinationPreambles_r17__cond FeatureCombinationPreambles_r17__Format.

Definition RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__Type := list FeatureCombinationPreambles_r17__Type.

Lemma RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__helper1 : (0 <= 1 <= maxFeatureCombPreamblesPerRACHResource_r17)%Z. unfold maxFeatureCombPreamblesPerRACHResource_r17.
 lia. Qed.
Lemma RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__helper2 : to_bit_sz (Z.to_nat (maxFeatureCombPreamblesPerRACHResource_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxFeatureCombPreamblesPerRACHResource_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__cond (z : RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxFeatureCombPreamblesPerRACHResource_r17)%Z /\ (list_and FeatureCombinationPreambles_r17__cond z) .

Record RACH_ConfigCommon__ext1O__Type : Set :=
  make__RACH_ConfigCommon__ext1O__Type {
    RACH_ConfigCommon__ext1O__ra_PrioritizationForSlicing_r17 : option RA_PrioritizationForSlicing_r17__Type ;
    RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17 : option RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__Type ;
}.
Definition RACH_ConfigCommon__ext1O__list := (
 Opt RA_PrioritizationForSlicing_r17__Type RA_PrioritizationForSlicing_r17__cond ::
 Opt RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__Type RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__cond ::
 nil).
Definition RACH_ConfigCommon__ext1O__cond z := 
  opt_cond RA_PrioritizationForSlicing_r17__cond (RACH_ConfigCommon__ext1O__ra_PrioritizationForSlicing_r17 z) /\
  opt_cond RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__cond (RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17 z) /\
  True.

Definition RACH_ConfigCommon__ext1__Type := RACH_ConfigCommon__ext1O__Type.
Definition RACH_ConfigCommon__ext1__cond := RACH_ConfigCommon__ext1O__cond.

Record RACH_ConfigCommon__Type : Set :=
  make__RACH_ConfigCommon__Type {
    RACH_ConfigCommon__rach_ConfigGeneric : RACH_ConfigGeneric__Type ;
    RACH_ConfigCommon__totalNumberOfRA_Preambles : option Z ;
    RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB : option RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type ;
    RACH_ConfigCommon__groupBconfigured : option RACH_ConfigCommon__groupBconfigured__Type ;
    RACH_ConfigCommon__ra_ContentionResolutionTimer : RACH_ConfigCommon__ra_ContentionResolutionTimer__Type ;
    RACH_ConfigCommon__rsrp_ThresholdSSB : option RSRP_Range__Type ;
    RACH_ConfigCommon__rsrp_ThresholdSSB_SUL : option RSRP_Range__Type ;
    RACH_ConfigCommon__prach_RootSequenceIndex : RACH_ConfigCommon__prach_RootSequenceIndex__Type ;
    RACH_ConfigCommon__msg1_SubcarrierSpacing : option SubcarrierSpacing__Type ;
    RACH_ConfigCommon__restrictedSetConfig : RACH_ConfigCommon__restrictedSetConfig__Type ;
    RACH_ConfigCommon__msg3_transformPrecoder : option RACH_ConfigCommon__msg3_transformPrecoder__Type ;
    RACH_ConfigCommon__ext0 : option RACH_ConfigCommon__ext0__Type ;
    RACH_ConfigCommon__ext1 : option RACH_ConfigCommon__ext1__Type ;
}.
Definition RACH_ConfigCommon__root_list : list seq_elem := (
 Nor RACH_ConfigGeneric__Type RACH_ConfigGeneric__cond ::
 Opt Z RACH_ConfigCommon__totalNumberOfRA_Preambles__cond ::
 Opt RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__cond ::
 Opt RACH_ConfigCommon__groupBconfigured__Type RACH_ConfigCommon__groupBconfigured__cond ::
 Nor RACH_ConfigCommon__ra_ContentionResolutionTimer__Type RACH_ConfigCommon__ra_ContentionResolutionTimer__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Nor RACH_ConfigCommon__prach_RootSequenceIndex__Type RACH_ConfigCommon__prach_RootSequenceIndex__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor RACH_ConfigCommon__restrictedSetConfig__Type RACH_ConfigCommon__restrictedSetConfig__cond ::
 Opt RACH_ConfigCommon__msg3_transformPrecoder__Type RACH_ConfigCommon__msg3_transformPrecoder__cond ::
 nil).
Definition RACH_ConfigCommon__ext_list : list typ := (
  typ_cons RACH_ConfigCommon__ext0__Type RACH_ConfigCommon__ext0__cond ::
  typ_cons RACH_ConfigCommon__ext1__Type RACH_ConfigCommon__ext1__cond ::
  nil).
Definition RACH_ConfigCommon__cond (z : RACH_ConfigCommon__Type) := 
(  RACH_ConfigGeneric__cond (RACH_ConfigCommon__rach_ConfigGeneric z) /\
  opt_cond RACH_ConfigCommon__totalNumberOfRA_Preambles__cond (RACH_ConfigCommon__totalNumberOfRA_Preambles z) /\
  opt_cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__cond (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB z) /\
  opt_cond RACH_ConfigCommon__groupBconfigured__cond (RACH_ConfigCommon__groupBconfigured z) /\
  RACH_ConfigCommon__ra_ContentionResolutionTimer__cond (RACH_ConfigCommon__ra_ContentionResolutionTimer z) /\
  opt_cond RSRP_Range__cond (RACH_ConfigCommon__rsrp_ThresholdSSB z) /\
  opt_cond RSRP_Range__cond (RACH_ConfigCommon__rsrp_ThresholdSSB_SUL z) /\
  RACH_ConfigCommon__prach_RootSequenceIndex__cond (RACH_ConfigCommon__prach_RootSequenceIndex z) /\
  opt_cond SubcarrierSpacing__cond (RACH_ConfigCommon__msg1_SubcarrierSpacing z) /\
  RACH_ConfigCommon__restrictedSetConfig__cond (RACH_ConfigCommon__restrictedSetConfig z) /\
  opt_cond RACH_ConfigCommon__msg3_transformPrecoder__cond (RACH_ConfigCommon__msg3_transformPrecoder z) /\
  True) /\ 
(  opt_cond RACH_ConfigCommon__ext0__cond (RACH_ConfigCommon__ext0 z) /\
  opt_cond RACH_ConfigCommon__ext1__cond (RACH_ConfigCommon__ext1 z) /\
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
Definition RACH_ConfigCommon__totalNumberOfRA_Preambles__Format : T_Format Z RACH_ConfigCommon__totalNumberOfRA_Preambles__cond :=
 ranged_int_format (1) (63) RACH_ConfigCommon__totalNumberOfRA_Preambles__helper1 RACH_ConfigCommon__totalNumberOfRA_Preambles__helper2.

Opaque RACH_ConfigCommon__totalNumberOfRA_Preambles__cond RACH_ConfigCommon__totalNumberOfRA_Preambles__Format.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Format : T_Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__nat__Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F1F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__F2F1.

Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Format.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Format : T_Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__nat__Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F1F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__F2F1.

Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Format.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Format : T_Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__nat__Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F1F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__F2F1.

Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Format.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Format : T_Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__nat__Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F1F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__F2F1.

Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Format.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Format : T_Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__nat__Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F1F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__F2F1.

Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Format.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__Format : T_Format Z RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__cond :=
 ranged_int_format (1) (16) RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__helper1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__helper2.

Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__Format.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__Format : T_Format Z RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__cond :=
 ranged_int_format (1) (8) RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__helper1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__helper2.

Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__Format.

Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__Format : T_Format Z RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__cond :=
 ranged_int_format (1) (4) RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__helper1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__helper2.

Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__Format.


Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Format_Type := Eval cbn in get_formats RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Format_list : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Format_Type :=
  (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Format, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Format, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Format, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Format, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Format, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four__Format, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight__Format, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen__Format, unit__Format)))))))).
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list__Format := Eval compute in choice_format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__len_helper1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__len_helper2  RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Format_list.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F1 (z : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type) : (choice RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list) :=
  match z with
   | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth t => existT _ 0 t
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth t => existT _ 1 t
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf t => existT _ 2 t
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one t => existT _ 3 t
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two t => existT _ 4 t
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four t => existT _ 5 t
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight t => existT _ 6 t
  | RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen t => existT _ 7 t
  end.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__g := (fun n => typ_set (get_nth_typ RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list n)).
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F2 (y : choice RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list) : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__g n -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type) with
    | 0 => fun (t : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth__Type) => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneEighth t 
    | 1 => fun (t : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth__Type) => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneFourth t 
    | 2 => fun (t : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf__Type) => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__oneHalf t 
    | 3 => fun (t : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one__Type) => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__one t 
    | 4 => fun (t : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two__Type) => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__two t 
    | 5 => fun (t : Z) => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__four t 
    | 6 => fun (t : Z) => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__eight t 
    | 7 => fun (t : Z) => RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__sixteen t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type with end) n0
           end t0).

Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__helper2 :  forall (y : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type), RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__cond y -> choice_cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__helper3 :  forall (y : RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type), RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F2 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__helper4 : (forall b : choice RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list, choice_cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list b -> RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__cond (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F2 b) /\ RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F1 (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F2.
Definition RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Format : T_Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Type RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__cond :=
  (* Eval compute in *) proj2_format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__list__Format RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F1 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__F2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__helper2 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__helper3 RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__helper4.
Opaque RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__cond RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Format.

Definition RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Format : T_Format RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__nat__Format RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F1 RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F2 RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F1F2 RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__F2F1.

Opaque RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__cond RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Format.

Definition RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Format : T_Format RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__nat__Format RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F1 RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F2 RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F1F2 RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__F2F1.

Opaque RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__cond RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Format.

Definition RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__Format : T_Format Z RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__cond :=
 ranged_int_format (1) (64) RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__helper1 RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__helper2.

Opaque RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__cond RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__Format.


Definition RACH_ConfigCommon__groupBconfigured__Format_Type := Eval cbn in seq_format_prod RACH_ConfigCommon__groupBconfigured__list.
Definition RACH_ConfigCommon__groupBconfigured__Format_list : RACH_ConfigCommon__groupBconfigured__Format_Type :=
  (RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA__Format, (RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB__Format, (RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA__Format, unit_format))).
Definition RACH_ConfigCommon__groupBconfigured__list__Format := (*Eval compute in *) seq_format RACH_ConfigCommon__groupBconfigured__list RACH_ConfigCommon__groupBconfigured__Format_list.
Definition RACH_ConfigCommon__groupBconfigured__F1 z :=
  (RACH_ConfigCommon__groupBconfigured__ra_Msg3SizeGroupA z, (RACH_ConfigCommon__groupBconfigured__messagePowerOffsetGroupB z, (RACH_ConfigCommon__groupBconfigured__numberOfRA_PreamblesGroupA z, tt))).
Definition RACH_ConfigCommon__groupBconfigured__F2 (y : seq_type RACH_ConfigCommon__groupBconfigured__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RACH_ConfigCommon__groupBconfigured__Type i0 i1 i2
  end.
Lemma RACH_ConfigCommon__groupBconfigured__F1F2_cond (z : RACH_ConfigCommon__groupBconfigured__Type)
  : RACH_ConfigCommon__groupBconfigured__cond z ->
  (seq_cond RACH_ConfigCommon__groupBconfigured__list (RACH_ConfigCommon__groupBconfigured__F1 z)).
intro H. unfold RACH_ConfigCommon__groupBconfigured__cond in H. simpl. auto. Qed.
Lemma RACH_ConfigCommon__groupBconfigured__F1F2_cond2 (z : RACH_ConfigCommon__groupBconfigured__Type)
 : RACH_ConfigCommon__groupBconfigured__F2 (RACH_ConfigCommon__groupBconfigured__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RACH_ConfigCommon__groupBconfigured__F2F1_cond (y : seq_type RACH_ConfigCommon__groupBconfigured__list)
  : seq_cond RACH_ConfigCommon__groupBconfigured__list y ->
 (RACH_ConfigCommon__groupBconfigured__cond (RACH_ConfigCommon__groupBconfigured__F2 y)) /\  RACH_ConfigCommon__groupBconfigured__F1 (RACH_ConfigCommon__groupBconfigured__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RACH_ConfigCommon__groupBconfigured__cond. simpl in *. auto.
 - simpl. unfold RACH_ConfigCommon__groupBconfigured__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RACH_ConfigCommon__groupBconfigured__Format : T_Format RACH_ConfigCommon__groupBconfigured__Type RACH_ConfigCommon__groupBconfigured__cond :=
        proj2_format  RACH_ConfigCommon__groupBconfigured__cond RACH_ConfigCommon__groupBconfigured__list__Format
    RACH_ConfigCommon__groupBconfigured__F1 RACH_ConfigCommon__groupBconfigured__F2 RACH_ConfigCommon__groupBconfigured__F1F2_cond  RACH_ConfigCommon__groupBconfigured__F1F2_cond2 RACH_ConfigCommon__groupBconfigured__F2F1_cond.
Opaque RACH_ConfigCommon__groupBconfigured__cond RACH_ConfigCommon__groupBconfigured__Format.

Definition RACH_ConfigCommon__ra_ContentionResolutionTimer__Format : T_Format RACH_ConfigCommon__ra_ContentionResolutionTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__ra_ContentionResolutionTimer__nat__Format RACH_ConfigCommon__ra_ContentionResolutionTimer__F1 RACH_ConfigCommon__ra_ContentionResolutionTimer__F2 RACH_ConfigCommon__ra_ContentionResolutionTimer__F1F2 RACH_ConfigCommon__ra_ContentionResolutionTimer__F2F1.

Opaque RACH_ConfigCommon__ra_ContentionResolutionTimer__cond RACH_ConfigCommon__ra_ContentionResolutionTimer__Format.

Definition RACH_ConfigCommon__prach_RootSequenceIndex__l839__Format : T_Format Z RACH_ConfigCommon__prach_RootSequenceIndex__l839__cond :=
 ranged_int_format (0) (837) RACH_ConfigCommon__prach_RootSequenceIndex__l839__helper1 RACH_ConfigCommon__prach_RootSequenceIndex__l839__helper2.

Opaque RACH_ConfigCommon__prach_RootSequenceIndex__l839__cond RACH_ConfigCommon__prach_RootSequenceIndex__l839__Format.

Definition RACH_ConfigCommon__prach_RootSequenceIndex__l139__Format : T_Format Z RACH_ConfigCommon__prach_RootSequenceIndex__l139__cond :=
 ranged_int_format (0) (137) RACH_ConfigCommon__prach_RootSequenceIndex__l139__helper1 RACH_ConfigCommon__prach_RootSequenceIndex__l139__helper2.

Opaque RACH_ConfigCommon__prach_RootSequenceIndex__l139__cond RACH_ConfigCommon__prach_RootSequenceIndex__l139__Format.


Definition RACH_ConfigCommon__prach_RootSequenceIndex__Format_Type := Eval cbn in get_formats RACH_ConfigCommon__prach_RootSequenceIndex__list.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__Format_list : RACH_ConfigCommon__prach_RootSequenceIndex__Format_Type :=
  (RACH_ConfigCommon__prach_RootSequenceIndex__l839__Format, (RACH_ConfigCommon__prach_RootSequenceIndex__l139__Format, unit__Format)).
Definition RACH_ConfigCommon__prach_RootSequenceIndex__list__Format := Eval compute in choice_format RACH_ConfigCommon__prach_RootSequenceIndex__list RACH_ConfigCommon__prach_RootSequenceIndex__len_helper1 RACH_ConfigCommon__prach_RootSequenceIndex__len_helper2  RACH_ConfigCommon__prach_RootSequenceIndex__Format_list.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__F1 (z : RACH_ConfigCommon__prach_RootSequenceIndex__Type) : (choice RACH_ConfigCommon__prach_RootSequenceIndex__list) :=
  match z with
   | RACH_ConfigCommon__prach_RootSequenceIndex__l839 t => existT _ 0 t
  | RACH_ConfigCommon__prach_RootSequenceIndex__l139 t => existT _ 1 t
  end.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__g := (fun n => typ_set (get_nth_typ RACH_ConfigCommon__prach_RootSequenceIndex__list n)).
Definition RACH_ConfigCommon__prach_RootSequenceIndex__F2 (y : choice RACH_ConfigCommon__prach_RootSequenceIndex__list) : RACH_ConfigCommon__prach_RootSequenceIndex__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RACH_ConfigCommon__prach_RootSequenceIndex__g n -> RACH_ConfigCommon__prach_RootSequenceIndex__Type) with
    | 0 => fun (t : Z) => RACH_ConfigCommon__prach_RootSequenceIndex__l839 t 
    | 1 => fun (t : Z) => RACH_ConfigCommon__prach_RootSequenceIndex__l139 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RACH_ConfigCommon__prach_RootSequenceIndex__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RACH_ConfigCommon__prach_RootSequenceIndex__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RACH_ConfigCommon__prach_RootSequenceIndex__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RACH_ConfigCommon__prach_RootSequenceIndex__Type with end) n0
           end t0).

Lemma RACH_ConfigCommon__prach_RootSequenceIndex__helper2 :  forall (y : RACH_ConfigCommon__prach_RootSequenceIndex__Type), RACH_ConfigCommon__prach_RootSequenceIndex__cond y -> choice_cond RACH_ConfigCommon__prach_RootSequenceIndex__list (RACH_ConfigCommon__prach_RootSequenceIndex__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RACH_ConfigCommon__prach_RootSequenceIndex__helper3 :  forall (y : RACH_ConfigCommon__prach_RootSequenceIndex__Type), RACH_ConfigCommon__prach_RootSequenceIndex__F2 (RACH_ConfigCommon__prach_RootSequenceIndex__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RACH_ConfigCommon__prach_RootSequenceIndex__helper4 : (forall b : choice RACH_ConfigCommon__prach_RootSequenceIndex__list, choice_cond RACH_ConfigCommon__prach_RootSequenceIndex__list b -> RACH_ConfigCommon__prach_RootSequenceIndex__cond (RACH_ConfigCommon__prach_RootSequenceIndex__F2 b) /\ RACH_ConfigCommon__prach_RootSequenceIndex__F1 (RACH_ConfigCommon__prach_RootSequenceIndex__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RACH_ConfigCommon__prach_RootSequenceIndex__F1 RACH_ConfigCommon__prach_RootSequenceIndex__F2.
Definition RACH_ConfigCommon__prach_RootSequenceIndex__Format : T_Format RACH_ConfigCommon__prach_RootSequenceIndex__Type RACH_ConfigCommon__prach_RootSequenceIndex__cond :=
  (* Eval compute in *) proj2_format RACH_ConfigCommon__prach_RootSequenceIndex__cond RACH_ConfigCommon__prach_RootSequenceIndex__list__Format RACH_ConfigCommon__prach_RootSequenceIndex__F1 RACH_ConfigCommon__prach_RootSequenceIndex__F2 RACH_ConfigCommon__prach_RootSequenceIndex__helper2 RACH_ConfigCommon__prach_RootSequenceIndex__helper3 RACH_ConfigCommon__prach_RootSequenceIndex__helper4.
Opaque RACH_ConfigCommon__prach_RootSequenceIndex__cond RACH_ConfigCommon__prach_RootSequenceIndex__Format.

Definition RACH_ConfigCommon__restrictedSetConfig__Format : T_Format RACH_ConfigCommon__restrictedSetConfig__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__restrictedSetConfig__nat__Format RACH_ConfigCommon__restrictedSetConfig__F1 RACH_ConfigCommon__restrictedSetConfig__F2 RACH_ConfigCommon__restrictedSetConfig__F1F2 RACH_ConfigCommon__restrictedSetConfig__F2F1.

Opaque RACH_ConfigCommon__restrictedSetConfig__cond RACH_ConfigCommon__restrictedSetConfig__Format.

Definition RACH_ConfigCommon__msg3_transformPrecoder__Format : T_Format RACH_ConfigCommon__msg3_transformPrecoder__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigCommon__msg3_transformPrecoder__nat__Format RACH_ConfigCommon__msg3_transformPrecoder__F1 RACH_ConfigCommon__msg3_transformPrecoder__F2 RACH_ConfigCommon__msg3_transformPrecoder__F1F2 RACH_ConfigCommon__msg3_transformPrecoder__F2F1.

Opaque RACH_ConfigCommon__msg3_transformPrecoder__cond RACH_ConfigCommon__msg3_transformPrecoder__Format.

Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__Format : T_Format RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__Type RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__cond RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__Format.


Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Format_Type := Eval cbn in seq_format_prod RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list.
Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Format_list : RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Format_Type :=
  (RA_Prioritization__Format, (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16__Format, unit_format)).
Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list__Format := (*Eval compute in *) seq_format RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Format_list.
Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1 z :=
  (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_Prioritization_r16 z, (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__ra_PrioritizationForAI_r16 z, tt)).
Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F2 (y : seq_type RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Type i0 i1
  end.
Lemma RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1F2_cond (z : RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Type)
  : RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond z ->
  (seq_cond RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1 z)).
intro H. unfold RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond in H. simpl. auto. Qed.
Lemma RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1F2_cond2 (z : RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Type)
 : RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F2 (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F2F1_cond (y : seq_type RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list)
  : seq_cond RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list y ->
 (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F2 y)) /\  RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1 (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond. simpl in *. auto.
 - simpl. unfold RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Format : T_Format RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Type RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond :=
        proj2_format  RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__list__Format
    RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1 RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F2 RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1F2_cond  RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F1F2_cond2 RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__F2F1_cond.
Opaque RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__cond RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Format.

Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__Format : T_Format Z RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__cond :=
 ranged_int_format (0) (569) RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__helper1 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__helper2.

Opaque RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__cond RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__Format.

Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__Format : T_Format Z RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__cond :=
 ranged_int_format (0) (1149) RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__helper1 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__helper2.

Opaque RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__cond RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__Format.


Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Format_Type := Eval cbn in get_formats RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Format_list : RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Format_Type :=
  (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571__Format, (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151__Format, unit__Format)).
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list__Format := Eval compute in choice_format RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__len_helper1 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__len_helper2  RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Format_list.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F1 (z : RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type) : (choice RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list) :=
  match z with
   | RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571 t => existT _ 0 t
  | RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151 t => existT _ 1 t
  end.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__g := (fun n => typ_set (get_nth_typ RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list n)).
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F2 (y : choice RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list) : RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__g n -> RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type) with
    | 0 => fun (t : Z) => RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l571 t 
    | 1 => fun (t : Z) => RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__l1151 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type with end) n0
           end t0).

Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__helper2 :  forall (y : RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type), RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__cond y -> choice_cond RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__helper3 :  forall (y : RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type), RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F2 (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__helper4 : (forall b : choice RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list, choice_cond RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list b -> RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__cond (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F2 b) /\ RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F1 (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F1 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F2.
Definition RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Format : T_Format RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Type RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__cond :=
  (* Eval compute in *) proj2_format RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__cond RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__list__Format RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F1 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__F2 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__helper2 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__helper3 RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__helper4.
Opaque RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__cond RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Format.


Definition RACH_ConfigCommon__ext0O__Format_Type := Eval cbn in seq_format_prod RACH_ConfigCommon__ext0O__list.
Definition RACH_ConfigCommon__ext0O__Format_list : RACH_ConfigCommon__ext0O__Format_Type :=
  (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16__Format, (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16__Format, unit_format)).
Definition RACH_ConfigCommon__ext0O__list__Format := (*Eval compute in *) seq_format RACH_ConfigCommon__ext0O__list RACH_ConfigCommon__ext0O__Format_list.
Definition RACH_ConfigCommon__ext0O__F1 z :=
  (RACH_ConfigCommon__ext0O__ra_PrioritizationForAccessIdentity_r16 z, (RACH_ConfigCommon__ext0O__prach_RootSequenceIndex_r16 z, tt)).
Definition RACH_ConfigCommon__ext0O__F2 (y : seq_type RACH_ConfigCommon__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RACH_ConfigCommon__ext0O__Type i0 i1
  end.
Lemma RACH_ConfigCommon__ext0O__F1F2_cond (z : RACH_ConfigCommon__ext0O__Type)
  : RACH_ConfigCommon__ext0O__cond z ->
  (seq_cond RACH_ConfigCommon__ext0O__list (RACH_ConfigCommon__ext0O__F1 z)).
intro H. unfold RACH_ConfigCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma RACH_ConfigCommon__ext0O__F1F2_cond2 (z : RACH_ConfigCommon__ext0O__Type)
 : RACH_ConfigCommon__ext0O__F2 (RACH_ConfigCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RACH_ConfigCommon__ext0O__F2F1_cond (y : seq_type RACH_ConfigCommon__ext0O__list)
  : seq_cond RACH_ConfigCommon__ext0O__list y ->
 (RACH_ConfigCommon__ext0O__cond (RACH_ConfigCommon__ext0O__F2 y)) /\  RACH_ConfigCommon__ext0O__F1 (RACH_ConfigCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RACH_ConfigCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold RACH_ConfigCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RACH_ConfigCommon__ext0O__Format : T_Format RACH_ConfigCommon__ext0O__Type RACH_ConfigCommon__ext0O__cond :=
        proj2_format  RACH_ConfigCommon__ext0O__cond RACH_ConfigCommon__ext0O__list__Format
    RACH_ConfigCommon__ext0O__F1 RACH_ConfigCommon__ext0O__F2 RACH_ConfigCommon__ext0O__F1F2_cond  RACH_ConfigCommon__ext0O__F1F2_cond2 RACH_ConfigCommon__ext0O__F2F1_cond.
Opaque RACH_ConfigCommon__ext0O__cond RACH_ConfigCommon__ext0O__Format.

Definition RACH_ConfigCommon__ext0__check_all_none (b : RACH_ConfigCommon__ext0O__Type) : bool :=
match b with 
  | make__RACH_ConfigCommon__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition RACH_ConfigCommon__ext0__Format : T_Format RACH_ConfigCommon__ext0__Type RACH_ConfigCommon__ext0__cond :=
  restrict_add_format RACH_ConfigCommon__ext0__check_all_none RACH_ConfigCommon__ext0O__Format.

Opaque RACH_ConfigCommon__ext0__cond RACH_ConfigCommon__ext0__Format.

Definition RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__Format : T_Format RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__Type RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__cond := seq_of_format FeatureCombinationPreambles_r17__Format 1 maxFeatureCombPreamblesPerRACHResource_r17 RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__helper1 RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__helper2.

Opaque RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__cond RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__Format.


Definition RACH_ConfigCommon__ext1O__Format_Type := Eval cbn in seq_format_prod RACH_ConfigCommon__ext1O__list.
Definition RACH_ConfigCommon__ext1O__Format_list : RACH_ConfigCommon__ext1O__Format_Type :=
  (RA_PrioritizationForSlicing_r17__Format, (RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17__Format, unit_format)).
Definition RACH_ConfigCommon__ext1O__list__Format := (*Eval compute in *) seq_format RACH_ConfigCommon__ext1O__list RACH_ConfigCommon__ext1O__Format_list.
Definition RACH_ConfigCommon__ext1O__F1 z :=
  (RACH_ConfigCommon__ext1O__ra_PrioritizationForSlicing_r17 z, (RACH_ConfigCommon__ext1O__featureCombinationPreamblesList_r17 z, tt)).
Definition RACH_ConfigCommon__ext1O__F2 (y : seq_type RACH_ConfigCommon__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RACH_ConfigCommon__ext1O__Type i0 i1
  end.
Lemma RACH_ConfigCommon__ext1O__F1F2_cond (z : RACH_ConfigCommon__ext1O__Type)
  : RACH_ConfigCommon__ext1O__cond z ->
  (seq_cond RACH_ConfigCommon__ext1O__list (RACH_ConfigCommon__ext1O__F1 z)).
intro H. unfold RACH_ConfigCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma RACH_ConfigCommon__ext1O__F1F2_cond2 (z : RACH_ConfigCommon__ext1O__Type)
 : RACH_ConfigCommon__ext1O__F2 (RACH_ConfigCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RACH_ConfigCommon__ext1O__F2F1_cond (y : seq_type RACH_ConfigCommon__ext1O__list)
  : seq_cond RACH_ConfigCommon__ext1O__list y ->
 (RACH_ConfigCommon__ext1O__cond (RACH_ConfigCommon__ext1O__F2 y)) /\  RACH_ConfigCommon__ext1O__F1 (RACH_ConfigCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RACH_ConfigCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold RACH_ConfigCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RACH_ConfigCommon__ext1O__Format : T_Format RACH_ConfigCommon__ext1O__Type RACH_ConfigCommon__ext1O__cond :=
        proj2_format  RACH_ConfigCommon__ext1O__cond RACH_ConfigCommon__ext1O__list__Format
    RACH_ConfigCommon__ext1O__F1 RACH_ConfigCommon__ext1O__F2 RACH_ConfigCommon__ext1O__F1F2_cond  RACH_ConfigCommon__ext1O__F1F2_cond2 RACH_ConfigCommon__ext1O__F2F1_cond.
Opaque RACH_ConfigCommon__ext1O__cond RACH_ConfigCommon__ext1O__Format.

Definition RACH_ConfigCommon__ext1__check_all_none (b : RACH_ConfigCommon__ext1O__Type) : bool :=
match b with 
  | make__RACH_ConfigCommon__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition RACH_ConfigCommon__ext1__Format : T_Format RACH_ConfigCommon__ext1__Type RACH_ConfigCommon__ext1__cond :=
  restrict_add_format RACH_ConfigCommon__ext1__check_all_none RACH_ConfigCommon__ext1O__Format.

Opaque RACH_ConfigCommon__ext1__cond RACH_ConfigCommon__ext1__Format.


Definition RACH_ConfigCommon__root_Format_Type := Eval cbn in seq_format_prod RACH_ConfigCommon__root_list.
Definition RACH_ConfigCommon__root_Format_list : RACH_ConfigCommon__root_Format_Type :=
  (RACH_ConfigGeneric__Format, (RACH_ConfigCommon__totalNumberOfRA_Preambles__Format, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB__Format, (RACH_ConfigCommon__groupBconfigured__Format, (RACH_ConfigCommon__ra_ContentionResolutionTimer__Format, (RSRP_Range__Format, (RSRP_Range__Format, (RACH_ConfigCommon__prach_RootSequenceIndex__Format, (SubcarrierSpacing__Format, (RACH_ConfigCommon__restrictedSetConfig__Format, (RACH_ConfigCommon__msg3_transformPrecoder__Format, unit_format))))))))))).

Definition RACH_ConfigCommon__ext_Format_Type := Eval cbn in get_formats RACH_ConfigCommon__ext_list.
Definition RACH_ConfigCommon__ext_Format_list : RACH_ConfigCommon__ext_Format_Type :=
  (RACH_ConfigCommon__ext0__Format, (RACH_ConfigCommon__ext1__Format, unit__Format)).

Definition RACH_ConfigCommon__list_type : Set := (seq_type RACH_ConfigCommon__root_list) * (seq_ext_type RACH_ConfigCommon__ext_list).
Definition RACH_ConfigCommon__list_cond (z : RACH_ConfigCommon__list_type) : Prop :=
        (seq_cond RACH_ConfigCommon__root_list (fst z)) /\ (seq_ext_cond RACH_ConfigCommon__ext_list (snd z)).
Definition RACH_ConfigCommon__list_format : T_Format RACH_ConfigCommon__list_type RACH_ConfigCommon__list_cond :=
 (* Eval compute in *) seq_ext_format RACH_ConfigCommon__root_list RACH_ConfigCommon__root_Format_list RACH_ConfigCommon__ext_list RACH_ConfigCommon__ext_Format_list.

Opaque RACH_ConfigCommon__list_format.
Definition RACH_ConfigCommon__F1 (z : RACH_ConfigCommon__Type) : RACH_ConfigCommon__list_type :=
  (((RACH_ConfigCommon__rach_ConfigGeneric z, (RACH_ConfigCommon__totalNumberOfRA_Preambles z, (RACH_ConfigCommon__ssb_perRACH_OccasionAndCB_PreamblesPerSSB z, (RACH_ConfigCommon__groupBconfigured z, (RACH_ConfigCommon__ra_ContentionResolutionTimer z, (RACH_ConfigCommon__rsrp_ThresholdSSB z, (RACH_ConfigCommon__rsrp_ThresholdSSB_SUL z, (RACH_ConfigCommon__prach_RootSequenceIndex z, (RACH_ConfigCommon__msg1_SubcarrierSpacing z, (RACH_ConfigCommon__restrictedSetConfig z, (RACH_ConfigCommon__msg3_transformPrecoder z, tt)))))))))))), (
(RACH_ConfigCommon__ext0 z, (RACH_ConfigCommon__ext1 z, tt)))).
Definition RACH_ConfigCommon__F2 (y : RACH_ConfigCommon__list_type) : RACH_ConfigCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, _))))))))))), (i0, (i1, _)))=>
    make__RACH_ConfigCommon__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 i0 i1
  end.
Definition RACH_ConfigCommon__helper1 : (forall a : RACH_ConfigCommon__Type, RACH_ConfigCommon__cond a -> RACH_ConfigCommon__list_cond (RACH_ConfigCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RACH_ConfigCommon__helper2 : (forall a : RACH_ConfigCommon__Type, RACH_ConfigCommon__F2 (RACH_ConfigCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RACH_ConfigCommon__helper3 : (forall b : RACH_ConfigCommon__list_type, RACH_ConfigCommon__list_cond b -> RACH_ConfigCommon__cond (RACH_ConfigCommon__F2 b) /\ RACH_ConfigCommon__F1 (RACH_ConfigCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RACH_ConfigCommon__cond, RACH_ConfigCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RACH_ConfigCommon__Format : T_Format RACH_ConfigCommon__Type RACH_ConfigCommon__cond :=
 proj2_format RACH_ConfigCommon__cond RACH_ConfigCommon__list_format  RACH_ConfigCommon__F1 RACH_ConfigCommon__F2 RACH_ConfigCommon__helper1 RACH_ConfigCommon__helper2 RACH_ConfigCommon__helper3.

Opaque RACH_ConfigCommon__cond RACH_ConfigCommon__Format.

