Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ConfiguredGrantConfig__frequencyHopping__Type : Set :=
 | ConfiguredGrantConfig__frequencyHopping__intraSlot
 | ConfiguredGrantConfig__frequencyHopping__interSlot
.
Definition ConfiguredGrantConfig__frequencyHopping__cond := (fun (_ : ConfiguredGrantConfig__frequencyHopping__Type) => True).
Lemma ConfiguredGrantConfig__frequencyHopping__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__frequencyHopping__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__frequencyHopping__nat__helper.

Definition ConfiguredGrantConfig__frequencyHopping__F1 t :=
  match t with
  | ConfiguredGrantConfig__frequencyHopping__intraSlot => 0
  | ConfiguredGrantConfig__frequencyHopping__interSlot => 1
  end.
Definition ConfiguredGrantConfig__frequencyHopping__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__frequencyHopping__intraSlot
  | 1 => ConfiguredGrantConfig__frequencyHopping__interSlot
  | _ => ConfiguredGrantConfig__frequencyHopping__intraSlot
  end.
Lemma ConfiguredGrantConfig__frequencyHopping__F1F2 : forall x : ConfiguredGrantConfig__frequencyHopping__Type, (ConfiguredGrantConfig__frequencyHopping__F1 x <= 1) /\ ConfiguredGrantConfig__frequencyHopping__F2 (ConfiguredGrantConfig__frequencyHopping__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__frequencyHopping__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__frequencyHopping__F1 (ConfiguredGrantConfig__frequencyHopping__F2 y) = y. enum_solve H y. Qed.

Require Import NR.DMRS_UplinkConfig.

Opaque DMRS_UplinkConfig__cond DMRS_UplinkConfig__Format.

Inductive ConfiguredGrantConfig__mcs_Table__Type : Set :=
 | ConfiguredGrantConfig__mcs_Table__qam256
 | ConfiguredGrantConfig__mcs_Table__qam64LowSE
.
Definition ConfiguredGrantConfig__mcs_Table__cond := (fun (_ : ConfiguredGrantConfig__mcs_Table__Type) => True).
Lemma ConfiguredGrantConfig__mcs_Table__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__mcs_Table__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__mcs_Table__nat__helper.

Definition ConfiguredGrantConfig__mcs_Table__F1 t :=
  match t with
  | ConfiguredGrantConfig__mcs_Table__qam256 => 0
  | ConfiguredGrantConfig__mcs_Table__qam64LowSE => 1
  end.
Definition ConfiguredGrantConfig__mcs_Table__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__mcs_Table__qam256
  | 1 => ConfiguredGrantConfig__mcs_Table__qam64LowSE
  | _ => ConfiguredGrantConfig__mcs_Table__qam256
  end.
Lemma ConfiguredGrantConfig__mcs_Table__F1F2 : forall x : ConfiguredGrantConfig__mcs_Table__Type, (ConfiguredGrantConfig__mcs_Table__F1 x <= 1) /\ ConfiguredGrantConfig__mcs_Table__F2 (ConfiguredGrantConfig__mcs_Table__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__mcs_Table__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__mcs_Table__F1 (ConfiguredGrantConfig__mcs_Table__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__mcs_TableTransformPrecoder__Type : Set :=
 | ConfiguredGrantConfig__mcs_TableTransformPrecoder__qam256
 | ConfiguredGrantConfig__mcs_TableTransformPrecoder__qam64LowSE
.
Definition ConfiguredGrantConfig__mcs_TableTransformPrecoder__cond := (fun (_ : ConfiguredGrantConfig__mcs_TableTransformPrecoder__Type) => True).
Lemma ConfiguredGrantConfig__mcs_TableTransformPrecoder__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__mcs_TableTransformPrecoder__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__mcs_TableTransformPrecoder__nat__helper.

Definition ConfiguredGrantConfig__mcs_TableTransformPrecoder__F1 t :=
  match t with
  | ConfiguredGrantConfig__mcs_TableTransformPrecoder__qam256 => 0
  | ConfiguredGrantConfig__mcs_TableTransformPrecoder__qam64LowSE => 1
  end.
Definition ConfiguredGrantConfig__mcs_TableTransformPrecoder__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__mcs_TableTransformPrecoder__qam256
  | 1 => ConfiguredGrantConfig__mcs_TableTransformPrecoder__qam64LowSE
  | _ => ConfiguredGrantConfig__mcs_TableTransformPrecoder__qam256
  end.
Lemma ConfiguredGrantConfig__mcs_TableTransformPrecoder__F1F2 : forall x : ConfiguredGrantConfig__mcs_TableTransformPrecoder__Type, (ConfiguredGrantConfig__mcs_TableTransformPrecoder__F1 x <= 1) /\ ConfiguredGrantConfig__mcs_TableTransformPrecoder__F2 (ConfiguredGrantConfig__mcs_TableTransformPrecoder__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__mcs_TableTransformPrecoder__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__mcs_TableTransformPrecoder__F1 (ConfiguredGrantConfig__mcs_TableTransformPrecoder__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.CG_UCI_OnPUSCH.
Definition ConfiguredGrantConfig__uci_OnPUSCH__Type := SetupRelease__Type CG_UCI_OnPUSCH__Type.
Definition ConfiguredGrantConfig__uci_OnPUSCH__cond := SetupRelease__cond _ CG_UCI_OnPUSCH__cond.
Definition ConfiguredGrantConfig__uci_OnPUSCH__Format : T_Format ConfiguredGrantConfig__uci_OnPUSCH__Type ConfiguredGrantConfig__uci_OnPUSCH__cond := SetupRelease__Format _ _ CG_UCI_OnPUSCH__Format.
Opaque ConfiguredGrantConfig__uci_OnPUSCH__cond ConfiguredGrantConfig__uci_OnPUSCH__Format.

Inductive ConfiguredGrantConfig__resourceAllocation__Type : Set :=
 | ConfiguredGrantConfig__resourceAllocation__resourceAllocationType0
 | ConfiguredGrantConfig__resourceAllocation__resourceAllocationType1
 | ConfiguredGrantConfig__resourceAllocation__dynamicSwitch
.
Definition ConfiguredGrantConfig__resourceAllocation__cond := (fun (_ : ConfiguredGrantConfig__resourceAllocation__Type) => True).
Lemma ConfiguredGrantConfig__resourceAllocation__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__resourceAllocation__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ConfiguredGrantConfig__resourceAllocation__nat__helper.

Definition ConfiguredGrantConfig__resourceAllocation__F1 t :=
  match t with
  | ConfiguredGrantConfig__resourceAllocation__resourceAllocationType0 => 0
  | ConfiguredGrantConfig__resourceAllocation__resourceAllocationType1 => 1
  | ConfiguredGrantConfig__resourceAllocation__dynamicSwitch => 2
  end.
Definition ConfiguredGrantConfig__resourceAllocation__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__resourceAllocation__resourceAllocationType0
  | 1 => ConfiguredGrantConfig__resourceAllocation__resourceAllocationType1
  | 2 => ConfiguredGrantConfig__resourceAllocation__dynamicSwitch
  | _ => ConfiguredGrantConfig__resourceAllocation__resourceAllocationType0
  end.
Lemma ConfiguredGrantConfig__resourceAllocation__F1F2 : forall x : ConfiguredGrantConfig__resourceAllocation__Type, (ConfiguredGrantConfig__resourceAllocation__F1 x <= 2) /\ ConfiguredGrantConfig__resourceAllocation__F2 (ConfiguredGrantConfig__resourceAllocation__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__resourceAllocation__F2F1 : forall (y : nat) (H : y <= 2), ConfiguredGrantConfig__resourceAllocation__F1 (ConfiguredGrantConfig__resourceAllocation__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__rbg_Size__Type : Set :=
 | ConfiguredGrantConfig__rbg_Size__config2
.
Definition ConfiguredGrantConfig__rbg_Size__cond := (fun (_ : ConfiguredGrantConfig__rbg_Size__Type) => True).
Lemma ConfiguredGrantConfig__rbg_Size__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__rbg_Size__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ConfiguredGrantConfig__rbg_Size__nat__helper.

Definition ConfiguredGrantConfig__rbg_Size__F1 t :=
  match t with
  | ConfiguredGrantConfig__rbg_Size__config2 => 0
  end.
Definition ConfiguredGrantConfig__rbg_Size__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__rbg_Size__config2
  | _ => ConfiguredGrantConfig__rbg_Size__config2
  end.
Lemma ConfiguredGrantConfig__rbg_Size__F1F2 : forall x : ConfiguredGrantConfig__rbg_Size__Type, (ConfiguredGrantConfig__rbg_Size__F1 x <= 0) /\ ConfiguredGrantConfig__rbg_Size__F2 (ConfiguredGrantConfig__rbg_Size__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__rbg_Size__F2F1 : forall (y : nat) (H : y <= 0), ConfiguredGrantConfig__rbg_Size__F1 (ConfiguredGrantConfig__rbg_Size__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__powerControlLoopToUse__Type : Set :=
 | ConfiguredGrantConfig__powerControlLoopToUse__n0
 | ConfiguredGrantConfig__powerControlLoopToUse__n1
.
Definition ConfiguredGrantConfig__powerControlLoopToUse__cond := (fun (_ : ConfiguredGrantConfig__powerControlLoopToUse__Type) => True).
Lemma ConfiguredGrantConfig__powerControlLoopToUse__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__powerControlLoopToUse__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__powerControlLoopToUse__nat__helper.

Definition ConfiguredGrantConfig__powerControlLoopToUse__F1 t :=
  match t with
  | ConfiguredGrantConfig__powerControlLoopToUse__n0 => 0
  | ConfiguredGrantConfig__powerControlLoopToUse__n1 => 1
  end.
Definition ConfiguredGrantConfig__powerControlLoopToUse__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__powerControlLoopToUse__n0
  | 1 => ConfiguredGrantConfig__powerControlLoopToUse__n1
  | _ => ConfiguredGrantConfig__powerControlLoopToUse__n0
  end.
Lemma ConfiguredGrantConfig__powerControlLoopToUse__F1F2 : forall x : ConfiguredGrantConfig__powerControlLoopToUse__Type, (ConfiguredGrantConfig__powerControlLoopToUse__F1 x <= 1) /\ ConfiguredGrantConfig__powerControlLoopToUse__F2 (ConfiguredGrantConfig__powerControlLoopToUse__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__powerControlLoopToUse__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__powerControlLoopToUse__F1 (ConfiguredGrantConfig__powerControlLoopToUse__F2 y) = y. enum_solve H y. Qed.

Require Import NR.P0_PUSCH_AlphaSetId.

Opaque P0_PUSCH_AlphaSetId__cond P0_PUSCH_AlphaSetId__Format.

Inductive ConfiguredGrantConfig__transformPrecoder__Type : Set :=
 | ConfiguredGrantConfig__transformPrecoder__enabled
 | ConfiguredGrantConfig__transformPrecoder__disabled
.
Definition ConfiguredGrantConfig__transformPrecoder__cond := (fun (_ : ConfiguredGrantConfig__transformPrecoder__Type) => True).
Lemma ConfiguredGrantConfig__transformPrecoder__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__transformPrecoder__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__transformPrecoder__nat__helper.

Definition ConfiguredGrantConfig__transformPrecoder__F1 t :=
  match t with
  | ConfiguredGrantConfig__transformPrecoder__enabled => 0
  | ConfiguredGrantConfig__transformPrecoder__disabled => 1
  end.
Definition ConfiguredGrantConfig__transformPrecoder__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__transformPrecoder__enabled
  | 1 => ConfiguredGrantConfig__transformPrecoder__disabled
  | _ => ConfiguredGrantConfig__transformPrecoder__enabled
  end.
Lemma ConfiguredGrantConfig__transformPrecoder__F1F2 : forall x : ConfiguredGrantConfig__transformPrecoder__Type, (ConfiguredGrantConfig__transformPrecoder__F1 x <= 1) /\ ConfiguredGrantConfig__transformPrecoder__F2 (ConfiguredGrantConfig__transformPrecoder__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__transformPrecoder__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__transformPrecoder__F1 (ConfiguredGrantConfig__transformPrecoder__F2 y) = y. enum_solve H y. Qed.

Lemma ConfiguredGrantConfig__nrofHARQ_Processes__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__nrofHARQ_Processes__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__nrofHARQ_Processes__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__nrofHARQ_Processes__Type := Z.
Definition ConfiguredGrantConfig__nrofHARQ_Processes__cond := (fun z => (1 <= z <= 16)%Z).
Inductive ConfiguredGrantConfig__repK__Type : Set :=
 | ConfiguredGrantConfig__repK__n1
 | ConfiguredGrantConfig__repK__n2
 | ConfiguredGrantConfig__repK__n4
 | ConfiguredGrantConfig__repK__n8
.
Definition ConfiguredGrantConfig__repK__cond := (fun (_ : ConfiguredGrantConfig__repK__Type) => True).
Lemma ConfiguredGrantConfig__repK__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__repK__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 ConfiguredGrantConfig__repK__nat__helper.

Definition ConfiguredGrantConfig__repK__F1 t :=
  match t with
  | ConfiguredGrantConfig__repK__n1 => 0
  | ConfiguredGrantConfig__repK__n2 => 1
  | ConfiguredGrantConfig__repK__n4 => 2
  | ConfiguredGrantConfig__repK__n8 => 3
  end.
Definition ConfiguredGrantConfig__repK__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__repK__n1
  | 1 => ConfiguredGrantConfig__repK__n2
  | 2 => ConfiguredGrantConfig__repK__n4
  | 3 => ConfiguredGrantConfig__repK__n8
  | _ => ConfiguredGrantConfig__repK__n1
  end.
Lemma ConfiguredGrantConfig__repK__F1F2 : forall x : ConfiguredGrantConfig__repK__Type, (ConfiguredGrantConfig__repK__F1 x <= 3) /\ ConfiguredGrantConfig__repK__F2 (ConfiguredGrantConfig__repK__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__repK__F2F1 : forall (y : nat) (H : y <= 3), ConfiguredGrantConfig__repK__F1 (ConfiguredGrantConfig__repK__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__repK_RV__Type : Set :=
 | ConfiguredGrantConfig__repK_RV__s1_0231
 | ConfiguredGrantConfig__repK_RV__s2_0303
 | ConfiguredGrantConfig__repK_RV__s3_0000
.
Definition ConfiguredGrantConfig__repK_RV__cond := (fun (_ : ConfiguredGrantConfig__repK_RV__Type) => True).
Lemma ConfiguredGrantConfig__repK_RV__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__repK_RV__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ConfiguredGrantConfig__repK_RV__nat__helper.

Definition ConfiguredGrantConfig__repK_RV__F1 t :=
  match t with
  | ConfiguredGrantConfig__repK_RV__s1_0231 => 0
  | ConfiguredGrantConfig__repK_RV__s2_0303 => 1
  | ConfiguredGrantConfig__repK_RV__s3_0000 => 2
  end.
Definition ConfiguredGrantConfig__repK_RV__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__repK_RV__s1_0231
  | 1 => ConfiguredGrantConfig__repK_RV__s2_0303
  | 2 => ConfiguredGrantConfig__repK_RV__s3_0000
  | _ => ConfiguredGrantConfig__repK_RV__s1_0231
  end.
Lemma ConfiguredGrantConfig__repK_RV__F1F2 : forall x : ConfiguredGrantConfig__repK_RV__Type, (ConfiguredGrantConfig__repK_RV__F1 x <= 2) /\ ConfiguredGrantConfig__repK_RV__F2 (ConfiguredGrantConfig__repK_RV__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__repK_RV__F2F1 : forall (y : nat) (H : y <= 2), ConfiguredGrantConfig__repK_RV__F1 (ConfiguredGrantConfig__repK_RV__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__periodicity__Type : Set :=
 | ConfiguredGrantConfig__periodicity__sym2
 | ConfiguredGrantConfig__periodicity__sym7
 | ConfiguredGrantConfig__periodicity__sym1x14
 | ConfiguredGrantConfig__periodicity__sym2x14
 | ConfiguredGrantConfig__periodicity__sym4x14
 | ConfiguredGrantConfig__periodicity__sym5x14
 | ConfiguredGrantConfig__periodicity__sym8x14
 | ConfiguredGrantConfig__periodicity__sym10x14
 | ConfiguredGrantConfig__periodicity__sym16x14
 | ConfiguredGrantConfig__periodicity__sym20x14
 | ConfiguredGrantConfig__periodicity__sym32x14
 | ConfiguredGrantConfig__periodicity__sym40x14
 | ConfiguredGrantConfig__periodicity__sym64x14
 | ConfiguredGrantConfig__periodicity__sym80x14
 | ConfiguredGrantConfig__periodicity__sym128x14
 | ConfiguredGrantConfig__periodicity__sym160x14
 | ConfiguredGrantConfig__periodicity__sym256x14
 | ConfiguredGrantConfig__periodicity__sym320x14
 | ConfiguredGrantConfig__periodicity__sym512x14
 | ConfiguredGrantConfig__periodicity__sym640x14
 | ConfiguredGrantConfig__periodicity__sym1024x14
 | ConfiguredGrantConfig__periodicity__sym1280x14
 | ConfiguredGrantConfig__periodicity__sym2560x14
 | ConfiguredGrantConfig__periodicity__sym5120x14
 | ConfiguredGrantConfig__periodicity__sym6
 | ConfiguredGrantConfig__periodicity__sym1x12
 | ConfiguredGrantConfig__periodicity__sym2x12
 | ConfiguredGrantConfig__periodicity__sym4x12
 | ConfiguredGrantConfig__periodicity__sym5x12
 | ConfiguredGrantConfig__periodicity__sym8x12
 | ConfiguredGrantConfig__periodicity__sym10x12
 | ConfiguredGrantConfig__periodicity__sym16x12
 | ConfiguredGrantConfig__periodicity__sym20x12
 | ConfiguredGrantConfig__periodicity__sym32x12
 | ConfiguredGrantConfig__periodicity__sym40x12
 | ConfiguredGrantConfig__periodicity__sym64x12
 | ConfiguredGrantConfig__periodicity__sym80x12
 | ConfiguredGrantConfig__periodicity__sym128x12
 | ConfiguredGrantConfig__periodicity__sym160x12
 | ConfiguredGrantConfig__periodicity__sym256x12
 | ConfiguredGrantConfig__periodicity__sym320x12
 | ConfiguredGrantConfig__periodicity__sym512x12
 | ConfiguredGrantConfig__periodicity__sym640x12
 | ConfiguredGrantConfig__periodicity__sym1280x12
 | ConfiguredGrantConfig__periodicity__sym2560x12
.
Definition ConfiguredGrantConfig__periodicity__cond := (fun (_ : ConfiguredGrantConfig__periodicity__Type) => True).
Lemma ConfiguredGrantConfig__periodicity__nat__helper : to_bit_sz 44 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__periodicity__nat__Format : T_Format nat (fun z => (z <= 44)) :=
  nat_enum_format 44 ConfiguredGrantConfig__periodicity__nat__helper.

Definition ConfiguredGrantConfig__periodicity__F1 t :=
  match t with
  | ConfiguredGrantConfig__periodicity__sym2 => 0
  | ConfiguredGrantConfig__periodicity__sym7 => 1
  | ConfiguredGrantConfig__periodicity__sym1x14 => 2
  | ConfiguredGrantConfig__periodicity__sym2x14 => 3
  | ConfiguredGrantConfig__periodicity__sym4x14 => 4
  | ConfiguredGrantConfig__periodicity__sym5x14 => 5
  | ConfiguredGrantConfig__periodicity__sym8x14 => 6
  | ConfiguredGrantConfig__periodicity__sym10x14 => 7
  | ConfiguredGrantConfig__periodicity__sym16x14 => 8
  | ConfiguredGrantConfig__periodicity__sym20x14 => 9
  | ConfiguredGrantConfig__periodicity__sym32x14 => 10
  | ConfiguredGrantConfig__periodicity__sym40x14 => 11
  | ConfiguredGrantConfig__periodicity__sym64x14 => 12
  | ConfiguredGrantConfig__periodicity__sym80x14 => 13
  | ConfiguredGrantConfig__periodicity__sym128x14 => 14
  | ConfiguredGrantConfig__periodicity__sym160x14 => 15
  | ConfiguredGrantConfig__periodicity__sym256x14 => 16
  | ConfiguredGrantConfig__periodicity__sym320x14 => 17
  | ConfiguredGrantConfig__periodicity__sym512x14 => 18
  | ConfiguredGrantConfig__periodicity__sym640x14 => 19
  | ConfiguredGrantConfig__periodicity__sym1024x14 => 20
  | ConfiguredGrantConfig__periodicity__sym1280x14 => 21
  | ConfiguredGrantConfig__periodicity__sym2560x14 => 22
  | ConfiguredGrantConfig__periodicity__sym5120x14 => 23
  | ConfiguredGrantConfig__periodicity__sym6 => 24
  | ConfiguredGrantConfig__periodicity__sym1x12 => 25
  | ConfiguredGrantConfig__periodicity__sym2x12 => 26
  | ConfiguredGrantConfig__periodicity__sym4x12 => 27
  | ConfiguredGrantConfig__periodicity__sym5x12 => 28
  | ConfiguredGrantConfig__periodicity__sym8x12 => 29
  | ConfiguredGrantConfig__periodicity__sym10x12 => 30
  | ConfiguredGrantConfig__periodicity__sym16x12 => 31
  | ConfiguredGrantConfig__periodicity__sym20x12 => 32
  | ConfiguredGrantConfig__periodicity__sym32x12 => 33
  | ConfiguredGrantConfig__periodicity__sym40x12 => 34
  | ConfiguredGrantConfig__periodicity__sym64x12 => 35
  | ConfiguredGrantConfig__periodicity__sym80x12 => 36
  | ConfiguredGrantConfig__periodicity__sym128x12 => 37
  | ConfiguredGrantConfig__periodicity__sym160x12 => 38
  | ConfiguredGrantConfig__periodicity__sym256x12 => 39
  | ConfiguredGrantConfig__periodicity__sym320x12 => 40
  | ConfiguredGrantConfig__periodicity__sym512x12 => 41
  | ConfiguredGrantConfig__periodicity__sym640x12 => 42
  | ConfiguredGrantConfig__periodicity__sym1280x12 => 43
  | ConfiguredGrantConfig__periodicity__sym2560x12 => 44
  end.
Definition ConfiguredGrantConfig__periodicity__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__periodicity__sym2
  | 1 => ConfiguredGrantConfig__periodicity__sym7
  | 2 => ConfiguredGrantConfig__periodicity__sym1x14
  | 3 => ConfiguredGrantConfig__periodicity__sym2x14
  | 4 => ConfiguredGrantConfig__periodicity__sym4x14
  | 5 => ConfiguredGrantConfig__periodicity__sym5x14
  | 6 => ConfiguredGrantConfig__periodicity__sym8x14
  | 7 => ConfiguredGrantConfig__periodicity__sym10x14
  | 8 => ConfiguredGrantConfig__periodicity__sym16x14
  | 9 => ConfiguredGrantConfig__periodicity__sym20x14
  | 10 => ConfiguredGrantConfig__periodicity__sym32x14
  | 11 => ConfiguredGrantConfig__periodicity__sym40x14
  | 12 => ConfiguredGrantConfig__periodicity__sym64x14
  | 13 => ConfiguredGrantConfig__periodicity__sym80x14
  | 14 => ConfiguredGrantConfig__periodicity__sym128x14
  | 15 => ConfiguredGrantConfig__periodicity__sym160x14
  | 16 => ConfiguredGrantConfig__periodicity__sym256x14
  | 17 => ConfiguredGrantConfig__periodicity__sym320x14
  | 18 => ConfiguredGrantConfig__periodicity__sym512x14
  | 19 => ConfiguredGrantConfig__periodicity__sym640x14
  | 20 => ConfiguredGrantConfig__periodicity__sym1024x14
  | 21 => ConfiguredGrantConfig__periodicity__sym1280x14
  | 22 => ConfiguredGrantConfig__periodicity__sym2560x14
  | 23 => ConfiguredGrantConfig__periodicity__sym5120x14
  | 24 => ConfiguredGrantConfig__periodicity__sym6
  | 25 => ConfiguredGrantConfig__periodicity__sym1x12
  | 26 => ConfiguredGrantConfig__periodicity__sym2x12
  | 27 => ConfiguredGrantConfig__periodicity__sym4x12
  | 28 => ConfiguredGrantConfig__periodicity__sym5x12
  | 29 => ConfiguredGrantConfig__periodicity__sym8x12
  | 30 => ConfiguredGrantConfig__periodicity__sym10x12
  | 31 => ConfiguredGrantConfig__periodicity__sym16x12
  | 32 => ConfiguredGrantConfig__periodicity__sym20x12
  | 33 => ConfiguredGrantConfig__periodicity__sym32x12
  | 34 => ConfiguredGrantConfig__periodicity__sym40x12
  | 35 => ConfiguredGrantConfig__periodicity__sym64x12
  | 36 => ConfiguredGrantConfig__periodicity__sym80x12
  | 37 => ConfiguredGrantConfig__periodicity__sym128x12
  | 38 => ConfiguredGrantConfig__periodicity__sym160x12
  | 39 => ConfiguredGrantConfig__periodicity__sym256x12
  | 40 => ConfiguredGrantConfig__periodicity__sym320x12
  | 41 => ConfiguredGrantConfig__periodicity__sym512x12
  | 42 => ConfiguredGrantConfig__periodicity__sym640x12
  | 43 => ConfiguredGrantConfig__periodicity__sym1280x12
  | 44 => ConfiguredGrantConfig__periodicity__sym2560x12
  | _ => ConfiguredGrantConfig__periodicity__sym2
  end.
Lemma ConfiguredGrantConfig__periodicity__F1F2 : forall x : ConfiguredGrantConfig__periodicity__Type, (ConfiguredGrantConfig__periodicity__F1 x <= 44) /\ ConfiguredGrantConfig__periodicity__F2 (ConfiguredGrantConfig__periodicity__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__periodicity__F2F1 : forall (y : nat) (H : y <= 44), ConfiguredGrantConfig__periodicity__F1 (ConfiguredGrantConfig__periodicity__F2 y) = y. enum_solve H y. Qed.

Lemma ConfiguredGrantConfig__configuredGrantTimer__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__configuredGrantTimer__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__configuredGrantTimer__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__configuredGrantTimer__Type := Z.
Definition ConfiguredGrantConfig__configuredGrantTimer__cond := (fun z => (1 <= z <= 64)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__cond := (fun z => (0 <= z <= 15)%Z).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__Type := bit_string_fixed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 18 /\ bit_string_len_prop (fst z) (snd z)).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__cond := (fun z => (0 <= z <= 31)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__cond := (fun z => (0 <= z <= 1)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__cond := (fun z => (0 <= z <= 63)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__cond := (fun z => (0 <= z <= 15)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__cond := (fun z => (0 <= z <= 31)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__helper1 : (1 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__cond := (fun z => (1 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__helper1 : (0 <= maxNrofPUSCH_PathlossReferenceRSs_1)%Z. unfold maxNrofPUSCH_PathlossReferenceRSs_1.
 lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__helper2 : to_bit_sz (Z.to_nat (maxNrofPUSCH_PathlossReferenceRSs_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUSCH_PathlossReferenceRSs_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__cond := (fun z => (0 <= z <= maxNrofPUSCH_PathlossReferenceRSs_1)%Z).
Inductive ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Type : Set :=
 | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__pusch_RepTypeA
 | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__pusch_RepTypeB
.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__cond := (fun (_ : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Type) => True).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__nat__helper.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F1 t :=
  match t with
  | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__pusch_RepTypeA => 0
  | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__pusch_RepTypeB => 1
  end.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__pusch_RepTypeA
  | 1 => ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__pusch_RepTypeB
  | _ => ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__pusch_RepTypeA
  end.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F1F2 : forall x : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Type, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F1 x <= 1) /\ ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F2 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F1 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Type : Set :=
 | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__interRepetition
 | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__interSlot
.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__cond := (fun (_ : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Type) => True).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__nat__helper.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F1 t :=
  match t with
  | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__interRepetition => 0
  | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__interSlot => 1
  end.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__interRepetition
  | 1 => ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__interSlot
  | _ => ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__interRepetition
  end.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F1F2 : forall x : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Type, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F1 x <= 1) /\ ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F2 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F1 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Type : Set :=
 | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__sfn512
.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__cond := (fun (_ : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Type) => True).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__nat__helper.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F1 t :=
  match t with
  | ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__sfn512 => 0
  end.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__sfn512
  | _ => ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__sfn512
  end.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F1F2 : forall x : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Type, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F1 x <= 0) /\ ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F2 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F2F1 : forall (y : nat) (H : y <= 0), ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F1 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F2 y) = y. enum_solve H y. Qed.

Record ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type : Set :=
  make__ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type {
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16 : option ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Type ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16 : option ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Type ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16 : option ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Type ;
}.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list := (
 Opt ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__cond ::
 Opt ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__cond ::
 Opt ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__cond ::
 nil).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond z := 
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16 z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16 z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16 z) /\
  True.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__Type := ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__cond := ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond.

Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__helper1 : (0 <= maxNrofPUSCH_PathlossReferenceRSs_1)%Z. unfold maxNrofPUSCH_PathlossReferenceRSs_1.
 lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPUSCH_PathlossReferenceRSs_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUSCH_PathlossReferenceRSs_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__cond := (fun z => (0 <= z <= maxNrofPUSCH_PathlossReferenceRSs_1)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__cond := (fun z => (0 <= z <= 15)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__cond := (fun z => (0 <= z <= 63)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__helper1 : (16 <= 63)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__helper2 : to_bit_sz (Z.to_nat (63 - 16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 16))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__cond := (fun z => (16 <= z <= 63)%Z).
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__helper1 : (0 <= 40959)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__helper2 : to_bit_sz (Z.to_nat (40959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__Type := Z.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__cond := (fun z => (0 <= z <= 40959)%Z).
Require Import NR.CG_SDT_Configuration_r17.

Opaque CG_SDT_Configuration_r17__cond CG_SDT_Configuration_r17__Format.

Record ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type : Set :=
  make__ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type {
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17 : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17 : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17 : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710 : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17 : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cg_SDT_Configuration_r17 : option CG_SDT_Configuration_r17__Type ;
}.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list := (
 Opt Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__cond ::
 Opt Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__cond ::
 Opt Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__cond ::
 Opt Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__cond ::
 Opt Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__cond ::
 Opt CG_SDT_Configuration_r17__Type CG_SDT_Configuration_r17__cond ::
 nil).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond z := 
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17 z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17 z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17 z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710 z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17 z) /\
  opt_cond CG_SDT_Configuration_r17__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cg_SDT_Configuration_r17 z) /\
  True.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__Type := ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__cond := ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond.

Record ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type : Set :=
  make__ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type {
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset : Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation : Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__Type ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort : Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers : Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS : Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex : Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0 : option ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__Type ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1 : option ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__Type ;
}.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_list : list seq_elem := (
 Nor Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__cond ::
 Nor Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__cond ::
 Nor ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__cond ::
 Nor Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__cond ::
 Opt Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__cond ::
 Nor Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__cond ::
 Opt Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__cond ::
 Nor Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__cond ::
 Opt Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__cond ::
 Nor Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__cond ::
 nil).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_list : list typ := (
  typ_cons ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__cond ::
  typ_cons ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__cond ::
  nil).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond (z : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type) := 
(  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset z) /\
  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation z) /\
  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation z) /\
  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization z) /\
  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator z) /\
  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset z) /\
  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex z) /\
  True) /\ 
(  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0 z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1 z) /\
  True).

Lemma ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__Type := Z.
Definition ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__cond := (fun z => (1 <= z <= 64)%Z).
Inductive ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Type : Set :=
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym7
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym1x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym2x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym3x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym4x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym5x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym6x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym7x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym8x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym9x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym10x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym11x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym12x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym13x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym14x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym15x14
 | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym16x14
.
Definition ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__cond := (fun (_ : ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Type) => True).
Lemma ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__nat__helper : to_bit_sz 16 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__nat__Format : T_Format nat (fun z => (z <= 16)) :=
  nat_enum_format 16 ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__nat__helper.

Definition ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F1 t :=
  match t with
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym7 => 0
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym1x14 => 1
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym2x14 => 2
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym3x14 => 3
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym4x14 => 4
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym5x14 => 5
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym6x14 => 6
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym7x14 => 7
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym8x14 => 8
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym9x14 => 9
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym10x14 => 10
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym11x14 => 11
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym12x14 => 12
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym13x14 => 13
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym14x14 => 14
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym15x14 => 15
  | ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym16x14 => 16
  end.
Definition ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym7
  | 1 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym1x14
  | 2 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym2x14
  | 3 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym3x14
  | 4 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym4x14
  | 5 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym5x14
  | 6 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym6x14
  | 7 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym7x14
  | 8 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym8x14
  | 9 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym9x14
  | 10 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym10x14
  | 11 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym11x14
  | 12 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym12x14
  | 13 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym13x14
  | 14 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym14x14
  | 15 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym15x14
  | 16 => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym16x14
  | _ => ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__sym7
  end.
Lemma ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F1F2 : forall x : ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Type, (ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F1 x <= 16) /\ ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F2 (ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F2F1 : forall (y : nat) (H : y <= 16), ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F1 (ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F2 y) = y. enum_solve H y. Qed.

Lemma ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__helper1 : (1 <= 7)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__helper2 : to_bit_sz (Z.to_nat (7 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__Type := Z.
Definition ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__cond := (fun z => (1 <= z <= 7)%Z).
Lemma ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__helper1 : (1 <= 40)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__helper2 : to_bit_sz (Z.to_nat (40 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__Type := Z.
Definition ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__cond := (fun z => (1 <= z <= 40)%Z).
Require Import NR.CG_StartingOffsets_r16.

Opaque CG_StartingOffsets_r16__cond CG_StartingOffsets_r16__Format.

Inductive ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Type : Set :=
 | ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__enabled
.
Definition ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__cond := (fun (_ : ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Type) => True).
Lemma ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__nat__helper.

Definition ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F1 t :=
  match t with
  | ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__enabled => 0
  end.
Definition ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__enabled
  | _ => ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__enabled
  end.
Lemma ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F1F2 : forall x : ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Type, (ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F1 x <= 0) /\ ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F2 (ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F2F1 : forall (y : nat) (H : y <= 0), ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F1 (ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F2 y) = y. enum_solve H y. Qed.

Lemma ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__helper1 : (1 <= 39)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__helper2 : to_bit_sz (Z.to_nat (39 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__Type := Z.
Definition ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__cond := (fun z => (1 <= z <= 39)%Z).
Lemma ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__Type := Z.
Definition ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__cond := (fun z => (0 <= z <= 31)%Z).
Require Import NR.CG_COT_Sharing_r16.

Opaque CG_COT_Sharing_r16__cond CG_COT_Sharing_r16__Format.

Definition ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__Type := list CG_COT_Sharing_r16__Type.

Lemma ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__helper1 : (0 <= 1 <= 1709)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__helper2 : to_bit_sz (Z.to_nat (1709 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1709 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__cond (z : ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__Type) :=  (1 <= Z.of_nat (length z) <= 1709)%Z /\ (list_and CG_COT_Sharing_r16__cond z) .

Lemma ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__Type := Z.
Definition ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__Type := Z.
Definition ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__cond := (fun z => (0 <= z <= 15)%Z).
Require Import NR.ConfiguredGrantConfigIndex_r16.

Opaque ConfiguredGrantConfigIndex_r16__cond ConfiguredGrantConfigIndex_r16__Format.

Require Import NR.ConfiguredGrantConfigIndexMAC_r16.

Opaque ConfiguredGrantConfigIndexMAC_r16__cond ConfiguredGrantConfigIndexMAC_r16__Format.

Lemma ConfiguredGrantConfig__ext0O__periodicityExt_r16__helper1 : (1 <= 5120)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext0O__periodicityExt_r16__helper2 : to_bit_sz (Z.to_nat (5120 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5120 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext0O__periodicityExt_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext0O__periodicityExt_r16__Type := Z.
Definition ConfiguredGrantConfig__ext0O__periodicityExt_r16__cond := (fun z => (1 <= z <= 5120)%Z).
Inductive ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Type : Set :=
 | ConfiguredGrantConfig__ext0O__startingFromRV0_r16__on
 | ConfiguredGrantConfig__ext0O__startingFromRV0_r16__off
.
Definition ConfiguredGrantConfig__ext0O__startingFromRV0_r16__cond := (fun (_ : ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Type) => True).
Lemma ConfiguredGrantConfig__ext0O__startingFromRV0_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__ext0O__startingFromRV0_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__ext0O__startingFromRV0_r16__nat__helper.

Definition ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F1 t :=
  match t with
  | ConfiguredGrantConfig__ext0O__startingFromRV0_r16__on => 0
  | ConfiguredGrantConfig__ext0O__startingFromRV0_r16__off => 1
  end.
Definition ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__ext0O__startingFromRV0_r16__on
  | 1 => ConfiguredGrantConfig__ext0O__startingFromRV0_r16__off
  | _ => ConfiguredGrantConfig__ext0O__startingFromRV0_r16__on
  end.
Lemma ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F1F2 : forall x : ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Type, (ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F1 x <= 1) /\ ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F2 (ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F1 (ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Type : Set :=
 | ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__p0
 | ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__p1
.
Definition ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__cond := (fun (_ : ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Type) => True).
Lemma ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__nat__helper.

Definition ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F1 t :=
  match t with
  | ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__p0 => 0
  | ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__p1 => 1
  end.
Definition ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__p0
  | 1 => ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__p1
  | _ => ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__p0
  end.
Lemma ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F1F2 : forall x : ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Type, (ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F1 x <= 1) /\ ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F2 (ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F1 (ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ConfiguredGrantConfig__ext0O__autonomousTx_r16__Type : Set :=
 | ConfiguredGrantConfig__ext0O__autonomousTx_r16__enabled
.
Definition ConfiguredGrantConfig__ext0O__autonomousTx_r16__cond := (fun (_ : ConfiguredGrantConfig__ext0O__autonomousTx_r16__Type) => True).
Lemma ConfiguredGrantConfig__ext0O__autonomousTx_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__ext0O__autonomousTx_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ConfiguredGrantConfig__ext0O__autonomousTx_r16__nat__helper.

Definition ConfiguredGrantConfig__ext0O__autonomousTx_r16__F1 t :=
  match t with
  | ConfiguredGrantConfig__ext0O__autonomousTx_r16__enabled => 0
  end.
Definition ConfiguredGrantConfig__ext0O__autonomousTx_r16__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__ext0O__autonomousTx_r16__enabled
  | _ => ConfiguredGrantConfig__ext0O__autonomousTx_r16__enabled
  end.
Lemma ConfiguredGrantConfig__ext0O__autonomousTx_r16__F1F2 : forall x : ConfiguredGrantConfig__ext0O__autonomousTx_r16__Type, (ConfiguredGrantConfig__ext0O__autonomousTx_r16__F1 x <= 0) /\ ConfiguredGrantConfig__ext0O__autonomousTx_r16__F2 (ConfiguredGrantConfig__ext0O__autonomousTx_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__ext0O__autonomousTx_r16__F2F1 : forall (y : nat) (H : y <= 0), ConfiguredGrantConfig__ext0O__autonomousTx_r16__F1 (ConfiguredGrantConfig__ext0O__autonomousTx_r16__F2 y) = y. enum_solve H y. Qed.

Record ConfiguredGrantConfig__ext0O__Type : Set :=
  make__ConfiguredGrantConfig__ext0O__Type {
    ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16 : option Z ;
    ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16 : option ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Type ;
    ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16 : option Z ;
    ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16 : option Z ;
    ConfiguredGrantConfig__ext0O__cg_StartingOffsets_r16 : option CG_StartingOffsets_r16__Type ;
    ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16 : option ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Type ;
    ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16 : option Z ;
    ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16 : option Z ;
    ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16 : option ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__Type ;
    ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16 : option Z ;
    ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16 : option Z ;
    ConfiguredGrantConfig__ext0O__configuredGrantConfigIndex_r16 : option ConfiguredGrantConfigIndex_r16__Type ;
    ConfiguredGrantConfig__ext0O__configuredGrantConfigIndexMAC_r16 : option ConfiguredGrantConfigIndexMAC_r16__Type ;
    ConfiguredGrantConfig__ext0O__periodicityExt_r16 : option Z ;
    ConfiguredGrantConfig__ext0O__startingFromRV0_r16 : option ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Type ;
    ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16 : option ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Type ;
    ConfiguredGrantConfig__ext0O__autonomousTx_r16 : option ConfiguredGrantConfig__ext0O__autonomousTx_r16__Type ;
}.
Definition ConfiguredGrantConfig__ext0O__list := (
 Opt Z ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__cond ::
 Opt ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Type ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__cond ::
 Opt Z ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__cond ::
 Opt Z ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__cond ::
 Opt CG_StartingOffsets_r16__Type CG_StartingOffsets_r16__cond ::
 Opt ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Type ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__cond ::
 Opt Z ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__cond ::
 Opt Z ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__cond ::
 Opt ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__Type ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__cond ::
 Opt Z ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__cond ::
 Opt Z ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__cond ::
 Opt ConfiguredGrantConfigIndex_r16__Type ConfiguredGrantConfigIndex_r16__cond ::
 Opt ConfiguredGrantConfigIndexMAC_r16__Type ConfiguredGrantConfigIndexMAC_r16__cond ::
 Opt Z ConfiguredGrantConfig__ext0O__periodicityExt_r16__cond ::
 Opt ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Type ConfiguredGrantConfig__ext0O__startingFromRV0_r16__cond ::
 Opt ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Type ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__cond ::
 Opt ConfiguredGrantConfig__ext0O__autonomousTx_r16__Type ConfiguredGrantConfig__ext0O__autonomousTx_r16__cond ::
 nil).
Definition ConfiguredGrantConfig__ext0O__cond z := 
  opt_cond ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__cond (ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__cond (ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__cond (ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__cond (ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16 z) /\
  opt_cond CG_StartingOffsets_r16__cond (ConfiguredGrantConfig__ext0O__cg_StartingOffsets_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__cond (ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__cond (ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__cond (ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__cond (ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__cond (ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__cond (ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16 z) /\
  opt_cond ConfiguredGrantConfigIndex_r16__cond (ConfiguredGrantConfig__ext0O__configuredGrantConfigIndex_r16 z) /\
  opt_cond ConfiguredGrantConfigIndexMAC_r16__cond (ConfiguredGrantConfig__ext0O__configuredGrantConfigIndexMAC_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__periodicityExt_r16__cond (ConfiguredGrantConfig__ext0O__periodicityExt_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__startingFromRV0_r16__cond (ConfiguredGrantConfig__ext0O__startingFromRV0_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__cond (ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16 z) /\
  opt_cond ConfiguredGrantConfig__ext0O__autonomousTx_r16__cond (ConfiguredGrantConfig__ext0O__autonomousTx_r16 z) /\
  True.

Definition ConfiguredGrantConfig__ext0__Type := ConfiguredGrantConfig__ext0O__Type.
Definition ConfiguredGrantConfig__ext0__cond := ConfiguredGrantConfig__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.BetaOffsetsCrossPriSelCG_r17.
Definition ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__Type := SetupRelease__Type BetaOffsetsCrossPriSelCG_r17__Type.
Definition ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__cond := SetupRelease__cond _ BetaOffsetsCrossPriSelCG_r17__cond.
Definition ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__Format : T_Format ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__Type ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__cond := SetupRelease__Format _ _ BetaOffsetsCrossPriSelCG_r17__Format.
Opaque ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__cond ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.BetaOffsetsCrossPriSelCG_r17.
Definition ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__Type := SetupRelease__Type BetaOffsetsCrossPriSelCG_r17__Type.
Definition ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__cond := SetupRelease__cond _ BetaOffsetsCrossPriSelCG_r17__cond.
Definition ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__Format : T_Format ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__Type ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__cond := SetupRelease__Format _ _ BetaOffsetsCrossPriSelCG_r17__Format.
Opaque ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__cond ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__Format.

Inductive ConfiguredGrantConfig__ext1O__mappingPattern_r17__Type : Set :=
 | ConfiguredGrantConfig__ext1O__mappingPattern_r17__cyclicMapping
 | ConfiguredGrantConfig__ext1O__mappingPattern_r17__sequentialMapping
.
Definition ConfiguredGrantConfig__ext1O__mappingPattern_r17__cond := (fun (_ : ConfiguredGrantConfig__ext1O__mappingPattern_r17__Type) => True).
Lemma ConfiguredGrantConfig__ext1O__mappingPattern_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__ext1O__mappingPattern_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__ext1O__mappingPattern_r17__nat__helper.

Definition ConfiguredGrantConfig__ext1O__mappingPattern_r17__F1 t :=
  match t with
  | ConfiguredGrantConfig__ext1O__mappingPattern_r17__cyclicMapping => 0
  | ConfiguredGrantConfig__ext1O__mappingPattern_r17__sequentialMapping => 1
  end.
Definition ConfiguredGrantConfig__ext1O__mappingPattern_r17__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__ext1O__mappingPattern_r17__cyclicMapping
  | 1 => ConfiguredGrantConfig__ext1O__mappingPattern_r17__sequentialMapping
  | _ => ConfiguredGrantConfig__ext1O__mappingPattern_r17__cyclicMapping
  end.
Lemma ConfiguredGrantConfig__ext1O__mappingPattern_r17__F1F2 : forall x : ConfiguredGrantConfig__ext1O__mappingPattern_r17__Type, (ConfiguredGrantConfig__ext1O__mappingPattern_r17__F1 x <= 1) /\ ConfiguredGrantConfig__ext1O__mappingPattern_r17__F2 (ConfiguredGrantConfig__ext1O__mappingPattern_r17__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__ext1O__mappingPattern_r17__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__ext1O__mappingPattern_r17__F1 (ConfiguredGrantConfig__ext1O__mappingPattern_r17__F2 y) = y. enum_solve H y. Qed.

Lemma ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__Type := Z.
Definition ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__cond := (fun z => (0 <= z <= 3)%Z).
Require Import NR.P0_PUSCH_AlphaSetId.

Opaque P0_PUSCH_AlphaSetId__cond P0_PUSCH_AlphaSetId__Format.

Inductive ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Type : Set :=
 | ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__n0
 | ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__n1
.
Definition ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__cond := (fun (_ : ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Type) => True).
Lemma ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__nat__helper.

Definition ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F1 t :=
  match t with
  | ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__n0 => 0
  | ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__n1 => 1
  end.
Definition ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__n0
  | 1 => ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__n1
  | _ => ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__n0
  end.
Lemma ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F1F2 : forall x : ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Type, (ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F1 x <= 1) /\ ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F2 (ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F2F1 : forall (y : nat) (H : y <= 1), ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F1 (ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CG_COT_Sharing_r17.

Opaque CG_COT_Sharing_r17__cond CG_COT_Sharing_r17__Format.

Definition ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__Type := list CG_COT_Sharing_r17__Type.

Lemma ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__helper1 : (0 <= 1 <= 50722)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__helper2 : to_bit_sz (Z.to_nat (50722 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (50722 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__cond (z : ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__Type) :=  (1 <= Z.of_nat (length z) <= 50722)%Z /\ (list_and CG_COT_Sharing_r17__cond z) .

Lemma ConfiguredGrantConfig__ext1O__periodicityExt_r17__helper1 : (1 <= 40960)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext1O__periodicityExt_r17__helper2 : to_bit_sz (Z.to_nat (40960 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40960 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext1O__periodicityExt_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext1O__periodicityExt_r17__Type := Z.
Definition ConfiguredGrantConfig__ext1O__periodicityExt_r17__cond := (fun z => (1 <= z <= 40960)%Z).
Inductive ConfiguredGrantConfig__ext1O__repK_v1710__Type : Set :=
 | ConfiguredGrantConfig__ext1O__repK_v1710__n12
 | ConfiguredGrantConfig__ext1O__repK_v1710__n16
 | ConfiguredGrantConfig__ext1O__repK_v1710__n24
 | ConfiguredGrantConfig__ext1O__repK_v1710__n32
.
Definition ConfiguredGrantConfig__ext1O__repK_v1710__cond := (fun (_ : ConfiguredGrantConfig__ext1O__repK_v1710__Type) => True).
Lemma ConfiguredGrantConfig__ext1O__repK_v1710__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfiguredGrantConfig__ext1O__repK_v1710__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 ConfiguredGrantConfig__ext1O__repK_v1710__nat__helper.

Definition ConfiguredGrantConfig__ext1O__repK_v1710__F1 t :=
  match t with
  | ConfiguredGrantConfig__ext1O__repK_v1710__n12 => 0
  | ConfiguredGrantConfig__ext1O__repK_v1710__n16 => 1
  | ConfiguredGrantConfig__ext1O__repK_v1710__n24 => 2
  | ConfiguredGrantConfig__ext1O__repK_v1710__n32 => 3
  end.
Definition ConfiguredGrantConfig__ext1O__repK_v1710__F2 n :=
  match n with
  | 0 => ConfiguredGrantConfig__ext1O__repK_v1710__n12
  | 1 => ConfiguredGrantConfig__ext1O__repK_v1710__n16
  | 2 => ConfiguredGrantConfig__ext1O__repK_v1710__n24
  | 3 => ConfiguredGrantConfig__ext1O__repK_v1710__n32
  | _ => ConfiguredGrantConfig__ext1O__repK_v1710__n12
  end.
Lemma ConfiguredGrantConfig__ext1O__repK_v1710__F1F2 : forall x : ConfiguredGrantConfig__ext1O__repK_v1710__Type, (ConfiguredGrantConfig__ext1O__repK_v1710__F1 x <= 3) /\ ConfiguredGrantConfig__ext1O__repK_v1710__F2 (ConfiguredGrantConfig__ext1O__repK_v1710__F1 x) = x. imp_solve. Qed.
Lemma ConfiguredGrantConfig__ext1O__repK_v1710__F2F1 : forall (y : nat) (H : y <= 3), ConfiguredGrantConfig__ext1O__repK_v1710__F1 (ConfiguredGrantConfig__ext1O__repK_v1710__F2 y) = y. enum_solve H y. Qed.

Lemma ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__helper1 : (17 <= 32)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__helper2 : to_bit_sz (Z.to_nat (32 - 17)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 17))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__Type := Z.
Definition ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__cond := (fun z => (17 <= z <= 32)%Z).
Lemma ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__helper1 : (16 <= 31)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__helper2 : to_bit_sz (Z.to_nat (31 - 16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 16))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__Type := Z.
Definition ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__cond := (fun z => (16 <= z <= 31)%Z).
Lemma ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__helper1 : (33 <= 288)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__helper2 : to_bit_sz (Z.to_nat (288 - 33)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (288 - 33))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__Type := Z.
Definition ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__cond := (fun z => (33 <= z <= 288)%Z).
Lemma ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__helper1 : (238 <= 3584)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__helper2 : to_bit_sz (Z.to_nat (3584 - 238)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3584 - 238))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__Type := Z.
Definition ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__cond := (fun z => (238 <= z <= 3584)%Z).
Record ConfiguredGrantConfig__ext1O__Type : Set :=
  make__ConfiguredGrantConfig__ext1O__Type {
    ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17 : option ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__Type ;
    ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17 : option ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__Type ;
    ConfiguredGrantConfig__ext1O__mappingPattern_r17 : option ConfiguredGrantConfig__ext1O__mappingPattern_r17__Type ;
    ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17 : option Z ;
    ConfiguredGrantConfig__ext1O__p0_PUSCH_Alpha2_r17 : option P0_PUSCH_AlphaSetId__Type ;
    ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17 : option ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Type ;
    ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17 : option ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__Type ;
    ConfiguredGrantConfig__ext1O__periodicityExt_r17 : option Z ;
    ConfiguredGrantConfig__ext1O__repK_v1710 : option ConfiguredGrantConfig__ext1O__repK_v1710__Type ;
    ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700 : option Z ;
    ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700 : option Z ;
    ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700 : option Z ;
    ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710 : option Z ;
}.
Definition ConfiguredGrantConfig__ext1O__list := (
 Opt ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__Type ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__cond ::
 Opt ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__Type ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__cond ::
 Opt ConfiguredGrantConfig__ext1O__mappingPattern_r17__Type ConfiguredGrantConfig__ext1O__mappingPattern_r17__cond ::
 Opt Z ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__cond ::
 Opt P0_PUSCH_AlphaSetId__Type P0_PUSCH_AlphaSetId__cond ::
 Opt ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Type ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__cond ::
 Opt ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__Type ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__cond ::
 Opt Z ConfiguredGrantConfig__ext1O__periodicityExt_r17__cond ::
 Opt ConfiguredGrantConfig__ext1O__repK_v1710__Type ConfiguredGrantConfig__ext1O__repK_v1710__cond ::
 Opt Z ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__cond ::
 Opt Z ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__cond ::
 Opt Z ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__cond ::
 Opt Z ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__cond ::
 nil).
Definition ConfiguredGrantConfig__ext1O__cond z := 
  opt_cond ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__cond (ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__cond (ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__mappingPattern_r17__cond (ConfiguredGrantConfig__ext1O__mappingPattern_r17 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__cond (ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17 z) /\
  opt_cond P0_PUSCH_AlphaSetId__cond (ConfiguredGrantConfig__ext1O__p0_PUSCH_Alpha2_r17 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__cond (ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__cond (ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__periodicityExt_r17__cond (ConfiguredGrantConfig__ext1O__periodicityExt_r17 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__repK_v1710__cond (ConfiguredGrantConfig__ext1O__repK_v1710 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__cond (ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__cond (ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__cond (ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700 z) /\
  opt_cond ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__cond (ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710 z) /\
  True.

Definition ConfiguredGrantConfig__ext1__Type := ConfiguredGrantConfig__ext1O__Type.
Definition ConfiguredGrantConfig__ext1__cond := ConfiguredGrantConfig__ext1O__cond.

Lemma ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__helper1 : (16 <= 31)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__helper2 : to_bit_sz (Z.to_nat (31 - 16)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 16))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__Type := Z.
Definition ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__cond := (fun z => (16 <= z <= 31)%Z).
Lemma ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__helper1 : (1 <= 320)%Z.  lia. Qed.
Lemma ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__helper2 : to_bit_sz (Z.to_nat (320 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (320 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__Type := Z.
Definition ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__cond := (fun z => (1 <= z <= 320)%Z).
Record ConfiguredGrantConfig__ext2O__Type : Set :=
  make__ConfiguredGrantConfig__ext2O__Type {
    ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730 : option Z ;
    ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17 : option Z ;
}.
Definition ConfiguredGrantConfig__ext2O__list := (
 Opt Z ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__cond ::
 Opt Z ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__cond ::
 nil).
Definition ConfiguredGrantConfig__ext2O__cond z := 
  opt_cond ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__cond (ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730 z) /\
  opt_cond ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__cond (ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17 z) /\
  True.

Definition ConfiguredGrantConfig__ext2__Type := ConfiguredGrantConfig__ext2O__Type.
Definition ConfiguredGrantConfig__ext2__cond := ConfiguredGrantConfig__ext2O__cond.

Record ConfiguredGrantConfig__Type : Set :=
  make__ConfiguredGrantConfig__Type {
    ConfiguredGrantConfig__frequencyHopping : option ConfiguredGrantConfig__frequencyHopping__Type ;
    ConfiguredGrantConfig__cg_DMRS_Configuration : DMRS_UplinkConfig__Type ;
    ConfiguredGrantConfig__mcs_Table : option ConfiguredGrantConfig__mcs_Table__Type ;
    ConfiguredGrantConfig__mcs_TableTransformPrecoder : option ConfiguredGrantConfig__mcs_TableTransformPrecoder__Type ;
    ConfiguredGrantConfig__uci_OnPUSCH : option ConfiguredGrantConfig__uci_OnPUSCH__Type ;
    ConfiguredGrantConfig__resourceAllocation : ConfiguredGrantConfig__resourceAllocation__Type ;
    ConfiguredGrantConfig__rbg_Size : option ConfiguredGrantConfig__rbg_Size__Type ;
    ConfiguredGrantConfig__powerControlLoopToUse : ConfiguredGrantConfig__powerControlLoopToUse__Type ;
    ConfiguredGrantConfig__p0_PUSCH_Alpha : P0_PUSCH_AlphaSetId__Type ;
    ConfiguredGrantConfig__transformPrecoder : option ConfiguredGrantConfig__transformPrecoder__Type ;
    ConfiguredGrantConfig__nrofHARQ_Processes : Z ;
    ConfiguredGrantConfig__repK : ConfiguredGrantConfig__repK__Type ;
    ConfiguredGrantConfig__repK_RV : option ConfiguredGrantConfig__repK_RV__Type ;
    ConfiguredGrantConfig__periodicity : ConfiguredGrantConfig__periodicity__Type ;
    ConfiguredGrantConfig__configuredGrantTimer : option Z ;
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant : option ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type ;
    ConfiguredGrantConfig__ext0 : option ConfiguredGrantConfig__ext0__Type ;
    ConfiguredGrantConfig__ext1 : option ConfiguredGrantConfig__ext1__Type ;
    ConfiguredGrantConfig__ext2 : option ConfiguredGrantConfig__ext2__Type ;
}.
Definition ConfiguredGrantConfig__root_list : list seq_elem := (
 Opt ConfiguredGrantConfig__frequencyHopping__Type ConfiguredGrantConfig__frequencyHopping__cond ::
 Nor DMRS_UplinkConfig__Type DMRS_UplinkConfig__cond ::
 Opt ConfiguredGrantConfig__mcs_Table__Type ConfiguredGrantConfig__mcs_Table__cond ::
 Opt ConfiguredGrantConfig__mcs_TableTransformPrecoder__Type ConfiguredGrantConfig__mcs_TableTransformPrecoder__cond ::
 Opt ConfiguredGrantConfig__uci_OnPUSCH__Type ConfiguredGrantConfig__uci_OnPUSCH__cond ::
 Nor ConfiguredGrantConfig__resourceAllocation__Type ConfiguredGrantConfig__resourceAllocation__cond ::
 Opt ConfiguredGrantConfig__rbg_Size__Type ConfiguredGrantConfig__rbg_Size__cond ::
 Nor ConfiguredGrantConfig__powerControlLoopToUse__Type ConfiguredGrantConfig__powerControlLoopToUse__cond ::
 Nor P0_PUSCH_AlphaSetId__Type P0_PUSCH_AlphaSetId__cond ::
 Opt ConfiguredGrantConfig__transformPrecoder__Type ConfiguredGrantConfig__transformPrecoder__cond ::
 Nor Z ConfiguredGrantConfig__nrofHARQ_Processes__cond ::
 Nor ConfiguredGrantConfig__repK__Type ConfiguredGrantConfig__repK__cond ::
 Opt ConfiguredGrantConfig__repK_RV__Type ConfiguredGrantConfig__repK_RV__cond ::
 Nor ConfiguredGrantConfig__periodicity__Type ConfiguredGrantConfig__periodicity__cond ::
 Opt Z ConfiguredGrantConfig__configuredGrantTimer__cond ::
 Opt ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond ::
 nil).
Definition ConfiguredGrantConfig__ext_list : list typ := (
  typ_cons ConfiguredGrantConfig__ext0__Type ConfiguredGrantConfig__ext0__cond ::
  typ_cons ConfiguredGrantConfig__ext1__Type ConfiguredGrantConfig__ext1__cond ::
  typ_cons ConfiguredGrantConfig__ext2__Type ConfiguredGrantConfig__ext2__cond ::
  nil).
Definition ConfiguredGrantConfig__cond (z : ConfiguredGrantConfig__Type) := 
(  opt_cond ConfiguredGrantConfig__frequencyHopping__cond (ConfiguredGrantConfig__frequencyHopping z) /\
  DMRS_UplinkConfig__cond (ConfiguredGrantConfig__cg_DMRS_Configuration z) /\
  opt_cond ConfiguredGrantConfig__mcs_Table__cond (ConfiguredGrantConfig__mcs_Table z) /\
  opt_cond ConfiguredGrantConfig__mcs_TableTransformPrecoder__cond (ConfiguredGrantConfig__mcs_TableTransformPrecoder z) /\
  opt_cond ConfiguredGrantConfig__uci_OnPUSCH__cond (ConfiguredGrantConfig__uci_OnPUSCH z) /\
  ConfiguredGrantConfig__resourceAllocation__cond (ConfiguredGrantConfig__resourceAllocation z) /\
  opt_cond ConfiguredGrantConfig__rbg_Size__cond (ConfiguredGrantConfig__rbg_Size z) /\
  ConfiguredGrantConfig__powerControlLoopToUse__cond (ConfiguredGrantConfig__powerControlLoopToUse z) /\
  P0_PUSCH_AlphaSetId__cond (ConfiguredGrantConfig__p0_PUSCH_Alpha z) /\
  opt_cond ConfiguredGrantConfig__transformPrecoder__cond (ConfiguredGrantConfig__transformPrecoder z) /\
  ConfiguredGrantConfig__nrofHARQ_Processes__cond (ConfiguredGrantConfig__nrofHARQ_Processes z) /\
  ConfiguredGrantConfig__repK__cond (ConfiguredGrantConfig__repK z) /\
  opt_cond ConfiguredGrantConfig__repK_RV__cond (ConfiguredGrantConfig__repK_RV z) /\
  ConfiguredGrantConfig__periodicity__cond (ConfiguredGrantConfig__periodicity z) /\
  opt_cond ConfiguredGrantConfig__configuredGrantTimer__cond (ConfiguredGrantConfig__configuredGrantTimer z) /\
  opt_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant z) /\
  True) /\ 
(  opt_cond ConfiguredGrantConfig__ext0__cond (ConfiguredGrantConfig__ext0 z) /\
  opt_cond ConfiguredGrantConfig__ext1__cond (ConfiguredGrantConfig__ext1 z) /\
  opt_cond ConfiguredGrantConfig__ext2__cond (ConfiguredGrantConfig__ext2 z) /\
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
Definition ConfiguredGrantConfig__frequencyHopping__Format : T_Format ConfiguredGrantConfig__frequencyHopping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__frequencyHopping__nat__Format ConfiguredGrantConfig__frequencyHopping__F1 ConfiguredGrantConfig__frequencyHopping__F2 ConfiguredGrantConfig__frequencyHopping__F1F2 ConfiguredGrantConfig__frequencyHopping__F2F1.

Opaque ConfiguredGrantConfig__frequencyHopping__cond ConfiguredGrantConfig__frequencyHopping__Format.

Definition ConfiguredGrantConfig__mcs_Table__Format : T_Format ConfiguredGrantConfig__mcs_Table__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__mcs_Table__nat__Format ConfiguredGrantConfig__mcs_Table__F1 ConfiguredGrantConfig__mcs_Table__F2 ConfiguredGrantConfig__mcs_Table__F1F2 ConfiguredGrantConfig__mcs_Table__F2F1.

Opaque ConfiguredGrantConfig__mcs_Table__cond ConfiguredGrantConfig__mcs_Table__Format.

Definition ConfiguredGrantConfig__mcs_TableTransformPrecoder__Format : T_Format ConfiguredGrantConfig__mcs_TableTransformPrecoder__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__mcs_TableTransformPrecoder__nat__Format ConfiguredGrantConfig__mcs_TableTransformPrecoder__F1 ConfiguredGrantConfig__mcs_TableTransformPrecoder__F2 ConfiguredGrantConfig__mcs_TableTransformPrecoder__F1F2 ConfiguredGrantConfig__mcs_TableTransformPrecoder__F2F1.

Opaque ConfiguredGrantConfig__mcs_TableTransformPrecoder__cond ConfiguredGrantConfig__mcs_TableTransformPrecoder__Format.

Opaque ConfiguredGrantConfig__uci_OnPUSCH__cond ConfiguredGrantConfig__uci_OnPUSCH__Format.

Definition ConfiguredGrantConfig__resourceAllocation__Format : T_Format ConfiguredGrantConfig__resourceAllocation__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__resourceAllocation__nat__Format ConfiguredGrantConfig__resourceAllocation__F1 ConfiguredGrantConfig__resourceAllocation__F2 ConfiguredGrantConfig__resourceAllocation__F1F2 ConfiguredGrantConfig__resourceAllocation__F2F1.

Opaque ConfiguredGrantConfig__resourceAllocation__cond ConfiguredGrantConfig__resourceAllocation__Format.

Definition ConfiguredGrantConfig__rbg_Size__Format : T_Format ConfiguredGrantConfig__rbg_Size__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__rbg_Size__nat__Format ConfiguredGrantConfig__rbg_Size__F1 ConfiguredGrantConfig__rbg_Size__F2 ConfiguredGrantConfig__rbg_Size__F1F2 ConfiguredGrantConfig__rbg_Size__F2F1.

Opaque ConfiguredGrantConfig__rbg_Size__cond ConfiguredGrantConfig__rbg_Size__Format.

Definition ConfiguredGrantConfig__powerControlLoopToUse__Format : T_Format ConfiguredGrantConfig__powerControlLoopToUse__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__powerControlLoopToUse__nat__Format ConfiguredGrantConfig__powerControlLoopToUse__F1 ConfiguredGrantConfig__powerControlLoopToUse__F2 ConfiguredGrantConfig__powerControlLoopToUse__F1F2 ConfiguredGrantConfig__powerControlLoopToUse__F2F1.

Opaque ConfiguredGrantConfig__powerControlLoopToUse__cond ConfiguredGrantConfig__powerControlLoopToUse__Format.

Definition ConfiguredGrantConfig__transformPrecoder__Format : T_Format ConfiguredGrantConfig__transformPrecoder__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__transformPrecoder__nat__Format ConfiguredGrantConfig__transformPrecoder__F1 ConfiguredGrantConfig__transformPrecoder__F2 ConfiguredGrantConfig__transformPrecoder__F1F2 ConfiguredGrantConfig__transformPrecoder__F2F1.

Opaque ConfiguredGrantConfig__transformPrecoder__cond ConfiguredGrantConfig__transformPrecoder__Format.

Definition ConfiguredGrantConfig__nrofHARQ_Processes__Format : T_Format Z ConfiguredGrantConfig__nrofHARQ_Processes__cond :=
 ranged_int_format (1) (16) ConfiguredGrantConfig__nrofHARQ_Processes__helper1 ConfiguredGrantConfig__nrofHARQ_Processes__helper2.

Opaque ConfiguredGrantConfig__nrofHARQ_Processes__cond ConfiguredGrantConfig__nrofHARQ_Processes__Format.

Definition ConfiguredGrantConfig__repK__Format : T_Format ConfiguredGrantConfig__repK__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__repK__nat__Format ConfiguredGrantConfig__repK__F1 ConfiguredGrantConfig__repK__F2 ConfiguredGrantConfig__repK__F1F2 ConfiguredGrantConfig__repK__F2F1.

Opaque ConfiguredGrantConfig__repK__cond ConfiguredGrantConfig__repK__Format.

Definition ConfiguredGrantConfig__repK_RV__Format : T_Format ConfiguredGrantConfig__repK_RV__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__repK_RV__nat__Format ConfiguredGrantConfig__repK_RV__F1 ConfiguredGrantConfig__repK_RV__F2 ConfiguredGrantConfig__repK_RV__F1F2 ConfiguredGrantConfig__repK_RV__F2F1.

Opaque ConfiguredGrantConfig__repK_RV__cond ConfiguredGrantConfig__repK_RV__Format.

Definition ConfiguredGrantConfig__periodicity__Format : T_Format ConfiguredGrantConfig__periodicity__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__periodicity__nat__Format ConfiguredGrantConfig__periodicity__F1 ConfiguredGrantConfig__periodicity__F2 ConfiguredGrantConfig__periodicity__F1F2 ConfiguredGrantConfig__periodicity__F2F1.

Opaque ConfiguredGrantConfig__periodicity__cond ConfiguredGrantConfig__periodicity__Format.

Definition ConfiguredGrantConfig__configuredGrantTimer__Format : T_Format Z ConfiguredGrantConfig__configuredGrantTimer__cond :=
 ranged_int_format (1) (64) ConfiguredGrantConfig__configuredGrantTimer__helper1 ConfiguredGrantConfig__configuredGrantTimer__helper2.

Opaque ConfiguredGrantConfig__configuredGrantTimer__cond ConfiguredGrantConfig__configuredGrantTimer__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__cond :=
 ranged_int_format (0) (5119) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__cond :=
 ranged_int_format (0) (15) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__cond := (* Eval compute in *) bit_string_fixed_format 18.
Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__cond :=
 ranged_int_format (0) (31) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__cond :=
 ranged_int_format (0) (1) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__cond :=
 ranged_int_format (0) (63) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__cond :=
 ranged_int_format (0) (15) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__cond :=
 ranged_int_format (0) (31) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__cond :=
 ranged_int_format (1) (maxNrofPhysicalResourceBlocks_1) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__cond :=
 ranged_int_format (0) (maxNrofPUSCH_PathlossReferenceRSs_1) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__nat__Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F1F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__F2F1.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__nat__Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F1F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__F2F1.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__nat__Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F1F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__F2F1.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Format.


Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Format_Type := Eval cbn in seq_format_prod ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Format_list : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Format_Type :=
  (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16__Format, unit_format))).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list__Format := (*Eval compute in *) seq_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Format_list.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1 z :=
  (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__pusch_RepTypeIndicator_r16 z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__frequencyHoppingPUSCH_RepTypeB_r16 z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__timeReferenceSFN_r16 z, tt))).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F2 (y : seq_type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type i0 i1 i2
  end.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1F2_cond (z : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type)
  : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond z ->
  (seq_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1 z)).
intro H. unfold ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond in H. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1F2_cond2 (z : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type)
 : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F2 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F2F1_cond (y : seq_type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list)
  : seq_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list y ->
 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F2 y)) /\  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond. simpl in *. auto.
 - simpl. unfold ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond :=
        proj2_format  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__list__Format
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1F2_cond  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F1F2_cond2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__F2F1_cond.
Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__check_all_none (b : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type) : bool :=
match b with 
  | make__ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__cond :=
  restrict_add_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__check_all_none ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0O__Format.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__cond :=
 ranged_int_format (0) (maxNrofPUSCH_PathlossReferenceRSs_1) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__cond :=
 ranged_int_format (0) (15) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__cond :=
 ranged_int_format (0) (63) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__cond :=
 ranged_int_format (16) (63) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__Format : T_Format Z ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__cond :=
 ranged_int_format (0) (40959) ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__helper2.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__Format.


Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Format_Type := Eval cbn in seq_format_prod ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Format_list : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Format_Type :=
  (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17__Format, (CG_SDT_Configuration_r17__Format, unit_format)))))).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list__Format := (*Eval compute in *) seq_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Format_list.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1 z :=
  (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__pathlossReferenceIndex2_r17 z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__srs_ResourceIndicator2_r17 z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__precodingAndNumberOfLayers2_r17 z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainAllocation_v1710 z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__timeDomainOffset_r17 z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cg_SDT_Configuration_r17 z, tt)))))).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F2 (y : seq_type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1F2_cond (z : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type)
  : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond z ->
  (seq_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1 z)).
intro H. unfold ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond in H. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1F2_cond2 (z : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type)
 : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F2 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F2F1_cond (y : seq_type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list)
  : seq_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list y ->
 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F2 y)) /\  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond. simpl in *. auto.
 - simpl. unfold ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond :=
        proj2_format  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__list__Format
    ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1F2_cond  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F1F2_cond2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__F2F1_cond.
Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Format.

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__check_all_none (b : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type) : bool :=
match b with 
  | make__ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__cond :=
  restrict_add_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__check_all_none ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1O__Format.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__Format.


Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_Format_Type := Eval cbn in seq_format_prod ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_list.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_Format_list : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_Format_Type :=
  (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex__Format, unit_format)))))))))).

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_Format_Type := Eval cbn in get_formats ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_list.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_Format_list : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_Format_Type :=
  (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1__Format, unit__Format)).

Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_type : Set := (seq_type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_list) * (seq_ext_type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_list).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_cond (z : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_type) : Prop :=
        (seq_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_list (fst z)) /\ (seq_ext_cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_list (snd z)).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_cond :=
 (* Eval compute in *) seq_ext_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_list ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__root_Format_list ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_list ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext_Format_list.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_format.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F1 (z : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type) : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_type :=
  (((ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainOffset z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__timeDomainAllocation z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyDomainAllocation z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__antennaPort z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__dmrs_SeqInitialization z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__precodingAndNumberOfLayers z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__srs_ResourceIndicator z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__mcsAndTBS z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__frequencyHoppingOffset z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__pathlossReferenceIndex z, tt))))))))))), (
(ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext0 z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__ext1 z, tt)))).
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F2 (y : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_type) : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, _)))))))))), (i0, (i1, _)))=>
    make__ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i0 i1
  end.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__helper1 : (forall a : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type, ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond a -> ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__helper2 : (forall a : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type, ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F2 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__helper3 : (forall b : ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_type, ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_cond b -> ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F2 b) /\ ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F1 (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond, ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Format : T_Format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Type ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond :=
 proj2_format ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__list_format  ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__F2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__helper1 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__helper2 ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__helper3.

Opaque ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__cond ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Format.

Definition ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__Format : T_Format Z ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__cond :=
 ranged_int_format (1) (64) ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__helper1 ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__cond ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__Format.

Definition ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Format : T_Format ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__nat__Format ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F1 ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F2 ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F1F2 ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__F2F1.

Opaque ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__cond ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Format.

Definition ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__Format : T_Format Z ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__cond :=
 ranged_int_format (1) (7) ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__helper1 ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__cond ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__Format.

Definition ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__Format : T_Format Z ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__cond :=
 ranged_int_format (1) (40) ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__helper1 ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__cond ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__Format.

Definition ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Format : T_Format ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__nat__Format ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F1 ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F2 ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F1F2 ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__F2F1.

Opaque ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__cond ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Format.

Definition ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__Format : T_Format Z ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__cond :=
 ranged_int_format (1) (39) ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__helper1 ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__cond ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__Format.

Definition ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__Format : T_Format Z ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__cond :=
 ranged_int_format (0) (31) ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__helper1 ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__cond ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__Format.

Definition ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__Format : T_Format ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__Type ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__cond := seq_of_format CG_COT_Sharing_r16__Format 1 1709 ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__helper1 ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__cond ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__Format.

Definition ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__Format : T_Format Z ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__cond :=
 ranged_int_format (0) (15) ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__helper1 ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__cond ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__Format.

Definition ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__Format : T_Format Z ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__cond :=
 ranged_int_format (0) (15) ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__helper1 ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__cond ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__Format.

Definition ConfiguredGrantConfig__ext0O__periodicityExt_r16__Format : T_Format Z ConfiguredGrantConfig__ext0O__periodicityExt_r16__cond :=
 ranged_int_format (1) (5120) ConfiguredGrantConfig__ext0O__periodicityExt_r16__helper1 ConfiguredGrantConfig__ext0O__periodicityExt_r16__helper2.

Opaque ConfiguredGrantConfig__ext0O__periodicityExt_r16__cond ConfiguredGrantConfig__ext0O__periodicityExt_r16__Format.

Definition ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Format : T_Format ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__ext0O__startingFromRV0_r16__nat__Format ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F1 ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F2 ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F1F2 ConfiguredGrantConfig__ext0O__startingFromRV0_r16__F2F1.

Opaque ConfiguredGrantConfig__ext0O__startingFromRV0_r16__cond ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Format.

Definition ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Format : T_Format ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__nat__Format ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F1 ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F2 ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F1F2 ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__F2F1.

Opaque ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__cond ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Format.

Definition ConfiguredGrantConfig__ext0O__autonomousTx_r16__Format : T_Format ConfiguredGrantConfig__ext0O__autonomousTx_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__ext0O__autonomousTx_r16__nat__Format ConfiguredGrantConfig__ext0O__autonomousTx_r16__F1 ConfiguredGrantConfig__ext0O__autonomousTx_r16__F2 ConfiguredGrantConfig__ext0O__autonomousTx_r16__F1F2 ConfiguredGrantConfig__ext0O__autonomousTx_r16__F2F1.

Opaque ConfiguredGrantConfig__ext0O__autonomousTx_r16__cond ConfiguredGrantConfig__ext0O__autonomousTx_r16__Format.


Definition ConfiguredGrantConfig__ext0O__Format_Type := Eval cbn in seq_format_prod ConfiguredGrantConfig__ext0O__list.
Definition ConfiguredGrantConfig__ext0O__Format_list : ConfiguredGrantConfig__ext0O__Format_Type :=
  (ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16__Format, (ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16__Format, (ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16__Format, (ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16__Format, (CG_StartingOffsets_r16__Format, (ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16__Format, (ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16__Format, (ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16__Format, (ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16__Format, (ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16__Format, (ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16__Format, (ConfiguredGrantConfigIndex_r16__Format, (ConfiguredGrantConfigIndexMAC_r16__Format, (ConfiguredGrantConfig__ext0O__periodicityExt_r16__Format, (ConfiguredGrantConfig__ext0O__startingFromRV0_r16__Format, (ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16__Format, (ConfiguredGrantConfig__ext0O__autonomousTx_r16__Format, unit_format))))))))))))))))).
Definition ConfiguredGrantConfig__ext0O__list__Format := (*Eval compute in *) seq_format ConfiguredGrantConfig__ext0O__list ConfiguredGrantConfig__ext0O__Format_list.
Definition ConfiguredGrantConfig__ext0O__F1 z :=
  (ConfiguredGrantConfig__ext0O__cg_RetransmissionTimer_r16 z, (ConfiguredGrantConfig__ext0O__cg_minDFI_Delay_r16 z, (ConfiguredGrantConfig__ext0O__cg_nrofPUSCH_InSlot_r16 z, (ConfiguredGrantConfig__ext0O__cg_nrofSlots_r16 z, (ConfiguredGrantConfig__ext0O__cg_StartingOffsets_r16 z, (ConfiguredGrantConfig__ext0O__cg_UCI_Multiplexing_r16 z, (ConfiguredGrantConfig__ext0O__cg_COT_SharingOffset_r16 z, (ConfiguredGrantConfig__ext0O__betaOffsetCG_UCI_r16 z, (ConfiguredGrantConfig__ext0O__cg_COT_SharingList_r16 z, (ConfiguredGrantConfig__ext0O__harq_ProcID_Offset_r16 z, (ConfiguredGrantConfig__ext0O__harq_ProcID_Offset2_r16 z, (ConfiguredGrantConfig__ext0O__configuredGrantConfigIndex_r16 z, (ConfiguredGrantConfig__ext0O__configuredGrantConfigIndexMAC_r16 z, (ConfiguredGrantConfig__ext0O__periodicityExt_r16 z, (ConfiguredGrantConfig__ext0O__startingFromRV0_r16 z, (ConfiguredGrantConfig__ext0O__phy_PriorityIndex_r16 z, (ConfiguredGrantConfig__ext0O__autonomousTx_r16 z, tt))))))))))))))))).
Definition ConfiguredGrantConfig__ext0O__F2 (y : seq_type ConfiguredGrantConfig__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, _)))))))))))))))))=>
    make__ConfiguredGrantConfig__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16
  end.
Lemma ConfiguredGrantConfig__ext0O__F1F2_cond (z : ConfiguredGrantConfig__ext0O__Type)
  : ConfiguredGrantConfig__ext0O__cond z ->
  (seq_cond ConfiguredGrantConfig__ext0O__list (ConfiguredGrantConfig__ext0O__F1 z)).
intro H. unfold ConfiguredGrantConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__ext0O__F1F2_cond2 (z : ConfiguredGrantConfig__ext0O__Type)
 : ConfiguredGrantConfig__ext0O__F2 (ConfiguredGrantConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__ext0O__F2F1_cond (y : seq_type ConfiguredGrantConfig__ext0O__list)
  : seq_cond ConfiguredGrantConfig__ext0O__list y ->
 (ConfiguredGrantConfig__ext0O__cond (ConfiguredGrantConfig__ext0O__F2 y)) /\  ConfiguredGrantConfig__ext0O__F1 (ConfiguredGrantConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfiguredGrantConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold ConfiguredGrantConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfiguredGrantConfig__ext0O__Format : T_Format ConfiguredGrantConfig__ext0O__Type ConfiguredGrantConfig__ext0O__cond :=
        proj2_format  ConfiguredGrantConfig__ext0O__cond ConfiguredGrantConfig__ext0O__list__Format
    ConfiguredGrantConfig__ext0O__F1 ConfiguredGrantConfig__ext0O__F2 ConfiguredGrantConfig__ext0O__F1F2_cond  ConfiguredGrantConfig__ext0O__F1F2_cond2 ConfiguredGrantConfig__ext0O__F2F1_cond.
Opaque ConfiguredGrantConfig__ext0O__cond ConfiguredGrantConfig__ext0O__Format.

Definition ConfiguredGrantConfig__ext0__check_all_none (b : ConfiguredGrantConfig__ext0O__Type) : bool :=
match b with 
  | make__ConfiguredGrantConfig__ext0O__Type None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition ConfiguredGrantConfig__ext0__Format : T_Format ConfiguredGrantConfig__ext0__Type ConfiguredGrantConfig__ext0__cond :=
  restrict_add_format ConfiguredGrantConfig__ext0__check_all_none ConfiguredGrantConfig__ext0O__Format.

Opaque ConfiguredGrantConfig__ext0__cond ConfiguredGrantConfig__ext0__Format.

Opaque ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__cond ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__Format.

Opaque ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__cond ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__Format.

Definition ConfiguredGrantConfig__ext1O__mappingPattern_r17__Format : T_Format ConfiguredGrantConfig__ext1O__mappingPattern_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__ext1O__mappingPattern_r17__nat__Format ConfiguredGrantConfig__ext1O__mappingPattern_r17__F1 ConfiguredGrantConfig__ext1O__mappingPattern_r17__F2 ConfiguredGrantConfig__ext1O__mappingPattern_r17__F1F2 ConfiguredGrantConfig__ext1O__mappingPattern_r17__F2F1.

Opaque ConfiguredGrantConfig__ext1O__mappingPattern_r17__cond ConfiguredGrantConfig__ext1O__mappingPattern_r17__Format.

Definition ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__Format : T_Format Z ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__cond :=
 ranged_int_format (0) (3) ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__helper1 ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__helper2.

Opaque ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__cond ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__Format.

Definition ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Format : T_Format ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__nat__Format ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F1 ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F2 ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F1F2 ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__F2F1.

Opaque ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__cond ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Format.

Definition ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__Format : T_Format ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__Type ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__cond := seq_of_format CG_COT_Sharing_r17__Format 1 50722 ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__helper1 ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__helper2.

Opaque ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__cond ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__Format.

Definition ConfiguredGrantConfig__ext1O__periodicityExt_r17__Format : T_Format Z ConfiguredGrantConfig__ext1O__periodicityExt_r17__cond :=
 ranged_int_format (1) (40960) ConfiguredGrantConfig__ext1O__periodicityExt_r17__helper1 ConfiguredGrantConfig__ext1O__periodicityExt_r17__helper2.

Opaque ConfiguredGrantConfig__ext1O__periodicityExt_r17__cond ConfiguredGrantConfig__ext1O__periodicityExt_r17__Format.

Definition ConfiguredGrantConfig__ext1O__repK_v1710__Format : T_Format ConfiguredGrantConfig__ext1O__repK_v1710__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfiguredGrantConfig__ext1O__repK_v1710__nat__Format ConfiguredGrantConfig__ext1O__repK_v1710__F1 ConfiguredGrantConfig__ext1O__repK_v1710__F2 ConfiguredGrantConfig__ext1O__repK_v1710__F1F2 ConfiguredGrantConfig__ext1O__repK_v1710__F2F1.

Opaque ConfiguredGrantConfig__ext1O__repK_v1710__cond ConfiguredGrantConfig__ext1O__repK_v1710__Format.

Definition ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__Format : T_Format Z ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__cond :=
 ranged_int_format (17) (32) ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__helper1 ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__helper2.

Opaque ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__cond ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__Format.

Definition ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__Format : T_Format Z ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__cond :=
 ranged_int_format (16) (31) ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__helper1 ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__helper2.

Opaque ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__cond ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__Format.

Definition ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__Format : T_Format Z ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__cond :=
 ranged_int_format (33) (288) ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__helper1 ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__helper2.

Opaque ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__cond ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__Format.

Definition ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__Format : T_Format Z ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__cond :=
 ranged_int_format (238) (3584) ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__helper1 ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__helper2.

Opaque ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__cond ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__Format.


Definition ConfiguredGrantConfig__ext1O__Format_Type := Eval cbn in seq_format_prod ConfiguredGrantConfig__ext1O__list.
Definition ConfiguredGrantConfig__ext1O__Format_list : ConfiguredGrantConfig__ext1O__Format_Type :=
  (ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17__Format, (ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17__Format, (ConfiguredGrantConfig__ext1O__mappingPattern_r17__Format, (ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17__Format, (P0_PUSCH_AlphaSetId__Format, (ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17__Format, (ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17__Format, (ConfiguredGrantConfig__ext1O__periodicityExt_r17__Format, (ConfiguredGrantConfig__ext1O__repK_v1710__Format, (ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700__Format, (ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700__Format, (ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700__Format, (ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710__Format, unit_format))))))))))))).
Definition ConfiguredGrantConfig__ext1O__list__Format := (*Eval compute in *) seq_format ConfiguredGrantConfig__ext1O__list ConfiguredGrantConfig__ext1O__Format_list.
Definition ConfiguredGrantConfig__ext1O__F1 z :=
  (ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri0_r17 z, (ConfiguredGrantConfig__ext1O__cg_betaOffsetsCrossPri1_r17 z, (ConfiguredGrantConfig__ext1O__mappingPattern_r17 z, (ConfiguredGrantConfig__ext1O__sequenceOffsetForRV_r17 z, (ConfiguredGrantConfig__ext1O__p0_PUSCH_Alpha2_r17 z, (ConfiguredGrantConfig__ext1O__powerControlLoopToUse2_r17 z, (ConfiguredGrantConfig__ext1O__cg_COT_SharingList_r17 z, (ConfiguredGrantConfig__ext1O__periodicityExt_r17 z, (ConfiguredGrantConfig__ext1O__repK_v1710 z, (ConfiguredGrantConfig__ext1O__nrofHARQ_Processes_v1700 z, (ConfiguredGrantConfig__ext1O__harq_ProcID_Offset2_v1700 z, (ConfiguredGrantConfig__ext1O__configuredGrantTimer_v1700 z, (ConfiguredGrantConfig__ext1O__cg_minDFI_Delay_v1710 z, tt))))))))))))).
Definition ConfiguredGrantConfig__ext1O__F2 (y : seq_type ConfiguredGrantConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, _)))))))))))))=>
    make__ConfiguredGrantConfig__ext1O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12
  end.
Lemma ConfiguredGrantConfig__ext1O__F1F2_cond (z : ConfiguredGrantConfig__ext1O__Type)
  : ConfiguredGrantConfig__ext1O__cond z ->
  (seq_cond ConfiguredGrantConfig__ext1O__list (ConfiguredGrantConfig__ext1O__F1 z)).
intro H. unfold ConfiguredGrantConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__ext1O__F1F2_cond2 (z : ConfiguredGrantConfig__ext1O__Type)
 : ConfiguredGrantConfig__ext1O__F2 (ConfiguredGrantConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__ext1O__F2F1_cond (y : seq_type ConfiguredGrantConfig__ext1O__list)
  : seq_cond ConfiguredGrantConfig__ext1O__list y ->
 (ConfiguredGrantConfig__ext1O__cond (ConfiguredGrantConfig__ext1O__F2 y)) /\  ConfiguredGrantConfig__ext1O__F1 (ConfiguredGrantConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfiguredGrantConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold ConfiguredGrantConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfiguredGrantConfig__ext1O__Format : T_Format ConfiguredGrantConfig__ext1O__Type ConfiguredGrantConfig__ext1O__cond :=
        proj2_format  ConfiguredGrantConfig__ext1O__cond ConfiguredGrantConfig__ext1O__list__Format
    ConfiguredGrantConfig__ext1O__F1 ConfiguredGrantConfig__ext1O__F2 ConfiguredGrantConfig__ext1O__F1F2_cond  ConfiguredGrantConfig__ext1O__F1F2_cond2 ConfiguredGrantConfig__ext1O__F2F1_cond.
Opaque ConfiguredGrantConfig__ext1O__cond ConfiguredGrantConfig__ext1O__Format.

Definition ConfiguredGrantConfig__ext1__check_all_none (b : ConfiguredGrantConfig__ext1O__Type) : bool :=
match b with 
  | make__ConfiguredGrantConfig__ext1O__Type None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition ConfiguredGrantConfig__ext1__Format : T_Format ConfiguredGrantConfig__ext1__Type ConfiguredGrantConfig__ext1__cond :=
  restrict_add_format ConfiguredGrantConfig__ext1__check_all_none ConfiguredGrantConfig__ext1O__Format.

Opaque ConfiguredGrantConfig__ext1__cond ConfiguredGrantConfig__ext1__Format.

Definition ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__Format : T_Format Z ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__cond :=
 ranged_int_format (16) (31) ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__helper1 ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__helper2.

Opaque ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__cond ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__Format.

Definition ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__Format : T_Format Z ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__cond :=
 ranged_int_format (1) (320) ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__helper1 ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__helper2.

Opaque ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__cond ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__Format.


Definition ConfiguredGrantConfig__ext2O__Format_Type := Eval cbn in seq_format_prod ConfiguredGrantConfig__ext2O__list.
Definition ConfiguredGrantConfig__ext2O__Format_list : ConfiguredGrantConfig__ext2O__Format_Type :=
  (ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730__Format, (ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17__Format, unit_format)).
Definition ConfiguredGrantConfig__ext2O__list__Format := (*Eval compute in *) seq_format ConfiguredGrantConfig__ext2O__list ConfiguredGrantConfig__ext2O__Format_list.
Definition ConfiguredGrantConfig__ext2O__F1 z :=
  (ConfiguredGrantConfig__ext2O__harq_ProcID_Offset_v1730 z, (ConfiguredGrantConfig__ext2O__cg_nrofSlots_r17 z, tt)).
Definition ConfiguredGrantConfig__ext2O__F2 (y : seq_type ConfiguredGrantConfig__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ConfiguredGrantConfig__ext2O__Type i0 i1
  end.
Lemma ConfiguredGrantConfig__ext2O__F1F2_cond (z : ConfiguredGrantConfig__ext2O__Type)
  : ConfiguredGrantConfig__ext2O__cond z ->
  (seq_cond ConfiguredGrantConfig__ext2O__list (ConfiguredGrantConfig__ext2O__F1 z)).
intro H. unfold ConfiguredGrantConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__ext2O__F1F2_cond2 (z : ConfiguredGrantConfig__ext2O__Type)
 : ConfiguredGrantConfig__ext2O__F2 (ConfiguredGrantConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfiguredGrantConfig__ext2O__F2F1_cond (y : seq_type ConfiguredGrantConfig__ext2O__list)
  : seq_cond ConfiguredGrantConfig__ext2O__list y ->
 (ConfiguredGrantConfig__ext2O__cond (ConfiguredGrantConfig__ext2O__F2 y)) /\  ConfiguredGrantConfig__ext2O__F1 (ConfiguredGrantConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfiguredGrantConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold ConfiguredGrantConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfiguredGrantConfig__ext2O__Format : T_Format ConfiguredGrantConfig__ext2O__Type ConfiguredGrantConfig__ext2O__cond :=
        proj2_format  ConfiguredGrantConfig__ext2O__cond ConfiguredGrantConfig__ext2O__list__Format
    ConfiguredGrantConfig__ext2O__F1 ConfiguredGrantConfig__ext2O__F2 ConfiguredGrantConfig__ext2O__F1F2_cond  ConfiguredGrantConfig__ext2O__F1F2_cond2 ConfiguredGrantConfig__ext2O__F2F1_cond.
Opaque ConfiguredGrantConfig__ext2O__cond ConfiguredGrantConfig__ext2O__Format.

Definition ConfiguredGrantConfig__ext2__check_all_none (b : ConfiguredGrantConfig__ext2O__Type) : bool :=
match b with 
  | make__ConfiguredGrantConfig__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition ConfiguredGrantConfig__ext2__Format : T_Format ConfiguredGrantConfig__ext2__Type ConfiguredGrantConfig__ext2__cond :=
  restrict_add_format ConfiguredGrantConfig__ext2__check_all_none ConfiguredGrantConfig__ext2O__Format.

Opaque ConfiguredGrantConfig__ext2__cond ConfiguredGrantConfig__ext2__Format.


Definition ConfiguredGrantConfig__root_Format_Type := Eval cbn in seq_format_prod ConfiguredGrantConfig__root_list.
Definition ConfiguredGrantConfig__root_Format_list : ConfiguredGrantConfig__root_Format_Type :=
  (ConfiguredGrantConfig__frequencyHopping__Format, (DMRS_UplinkConfig__Format, (ConfiguredGrantConfig__mcs_Table__Format, (ConfiguredGrantConfig__mcs_TableTransformPrecoder__Format, (ConfiguredGrantConfig__uci_OnPUSCH__Format, (ConfiguredGrantConfig__resourceAllocation__Format, (ConfiguredGrantConfig__rbg_Size__Format, (ConfiguredGrantConfig__powerControlLoopToUse__Format, (P0_PUSCH_AlphaSetId__Format, (ConfiguredGrantConfig__transformPrecoder__Format, (ConfiguredGrantConfig__nrofHARQ_Processes__Format, (ConfiguredGrantConfig__repK__Format, (ConfiguredGrantConfig__repK_RV__Format, (ConfiguredGrantConfig__periodicity__Format, (ConfiguredGrantConfig__configuredGrantTimer__Format, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant__Format, unit_format)))))))))))))))).

Definition ConfiguredGrantConfig__ext_Format_Type := Eval cbn in get_formats ConfiguredGrantConfig__ext_list.
Definition ConfiguredGrantConfig__ext_Format_list : ConfiguredGrantConfig__ext_Format_Type :=
  (ConfiguredGrantConfig__ext0__Format, (ConfiguredGrantConfig__ext1__Format, (ConfiguredGrantConfig__ext2__Format, unit__Format))).

Definition ConfiguredGrantConfig__list_type : Set := (seq_type ConfiguredGrantConfig__root_list) * (seq_ext_type ConfiguredGrantConfig__ext_list).
Definition ConfiguredGrantConfig__list_cond (z : ConfiguredGrantConfig__list_type) : Prop :=
        (seq_cond ConfiguredGrantConfig__root_list (fst z)) /\ (seq_ext_cond ConfiguredGrantConfig__ext_list (snd z)).
Definition ConfiguredGrantConfig__list_format : T_Format ConfiguredGrantConfig__list_type ConfiguredGrantConfig__list_cond :=
 (* Eval compute in *) seq_ext_format ConfiguredGrantConfig__root_list ConfiguredGrantConfig__root_Format_list ConfiguredGrantConfig__ext_list ConfiguredGrantConfig__ext_Format_list.

Opaque ConfiguredGrantConfig__list_format.
Definition ConfiguredGrantConfig__F1 (z : ConfiguredGrantConfig__Type) : ConfiguredGrantConfig__list_type :=
  (((ConfiguredGrantConfig__frequencyHopping z, (ConfiguredGrantConfig__cg_DMRS_Configuration z, (ConfiguredGrantConfig__mcs_Table z, (ConfiguredGrantConfig__mcs_TableTransformPrecoder z, (ConfiguredGrantConfig__uci_OnPUSCH z, (ConfiguredGrantConfig__resourceAllocation z, (ConfiguredGrantConfig__rbg_Size z, (ConfiguredGrantConfig__powerControlLoopToUse z, (ConfiguredGrantConfig__p0_PUSCH_Alpha z, (ConfiguredGrantConfig__transformPrecoder z, (ConfiguredGrantConfig__nrofHARQ_Processes z, (ConfiguredGrantConfig__repK z, (ConfiguredGrantConfig__repK_RV z, (ConfiguredGrantConfig__periodicity z, (ConfiguredGrantConfig__configuredGrantTimer z, (ConfiguredGrantConfig__rrc_ConfiguredUplinkGrant z, tt))))))))))))))))), (
(ConfiguredGrantConfig__ext0 z, (ConfiguredGrantConfig__ext1 z, (ConfiguredGrantConfig__ext2 z, tt))))).
Definition ConfiguredGrantConfig__F2 (y : ConfiguredGrantConfig__list_type) : ConfiguredGrantConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, _)))))))))))))))), (i0, (i1, (i2, _))))=>
    make__ConfiguredGrantConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 i0 i1 i2
  end.
Definition ConfiguredGrantConfig__helper1 : (forall a : ConfiguredGrantConfig__Type, ConfiguredGrantConfig__cond a -> ConfiguredGrantConfig__list_cond (ConfiguredGrantConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ConfiguredGrantConfig__helper2 : (forall a : ConfiguredGrantConfig__Type, ConfiguredGrantConfig__F2 (ConfiguredGrantConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ConfiguredGrantConfig__helper3 : (forall b : ConfiguredGrantConfig__list_type, ConfiguredGrantConfig__list_cond b -> ConfiguredGrantConfig__cond (ConfiguredGrantConfig__F2 b) /\ ConfiguredGrantConfig__F1 (ConfiguredGrantConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ConfiguredGrantConfig__cond, ConfiguredGrantConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ConfiguredGrantConfig__Format : T_Format ConfiguredGrantConfig__Type ConfiguredGrantConfig__cond :=
 proj2_format ConfiguredGrantConfig__cond ConfiguredGrantConfig__list_format  ConfiguredGrantConfig__F1 ConfiguredGrantConfig__F2 ConfiguredGrantConfig__helper1 ConfiguredGrantConfig__helper2 ConfiguredGrantConfig__helper3.

Opaque ConfiguredGrantConfig__cond ConfiguredGrantConfig__Format.

