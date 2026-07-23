Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PUSCH_Allocation_r16__mappingType_r16__Type : Set :=
 | PUSCH_Allocation_r16__mappingType_r16__typeA
 | PUSCH_Allocation_r16__mappingType_r16__typeB
.
Definition PUSCH_Allocation_r16__mappingType_r16__cond := (fun (_ : PUSCH_Allocation_r16__mappingType_r16__Type) => True).
Lemma PUSCH_Allocation_r16__mappingType_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Allocation_r16__mappingType_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Allocation_r16__mappingType_r16__nat__helper.

Definition PUSCH_Allocation_r16__mappingType_r16__F1 t :=
  match t with
  | PUSCH_Allocation_r16__mappingType_r16__typeA => 0
  | PUSCH_Allocation_r16__mappingType_r16__typeB => 1
  end.
Definition PUSCH_Allocation_r16__mappingType_r16__F2 n :=
  match n with
  | 0 => PUSCH_Allocation_r16__mappingType_r16__typeA
  | 1 => PUSCH_Allocation_r16__mappingType_r16__typeB
  | _ => PUSCH_Allocation_r16__mappingType_r16__typeA
  end.
Lemma PUSCH_Allocation_r16__mappingType_r16__F1F2 : forall x : PUSCH_Allocation_r16__mappingType_r16__Type, (PUSCH_Allocation_r16__mappingType_r16__F1 x <= 1) /\ PUSCH_Allocation_r16__mappingType_r16__F2 (PUSCH_Allocation_r16__mappingType_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Allocation_r16__mappingType_r16__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Allocation_r16__mappingType_r16__F1 (PUSCH_Allocation_r16__mappingType_r16__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_Allocation_r16__startSymbolAndLength_r16__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma PUSCH_Allocation_r16__startSymbolAndLength_r16__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Allocation_r16__startSymbolAndLength_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Allocation_r16__startSymbolAndLength_r16__Type := Z.
Definition PUSCH_Allocation_r16__startSymbolAndLength_r16__cond := (fun z => (0 <= z <= 127)%Z).
Lemma PUSCH_Allocation_r16__startSymbol_r16__helper1 : (0 <= 13)%Z.  lia. Qed.
Lemma PUSCH_Allocation_r16__startSymbol_r16__helper2 : to_bit_sz (Z.to_nat (13 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (13 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Allocation_r16__startSymbol_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Allocation_r16__startSymbol_r16__Type := Z.
Definition PUSCH_Allocation_r16__startSymbol_r16__cond := (fun z => (0 <= z <= 13)%Z).
Lemma PUSCH_Allocation_r16__length_r16__helper1 : (1 <= 14)%Z.  lia. Qed.
Lemma PUSCH_Allocation_r16__length_r16__helper2 : to_bit_sz (Z.to_nat (14 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (14 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Allocation_r16__length_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Allocation_r16__length_r16__Type := Z.
Definition PUSCH_Allocation_r16__length_r16__cond := (fun z => (1 <= z <= 14)%Z).
Inductive PUSCH_Allocation_r16__numberOfRepetitions_r16__Type : Set :=
 | PUSCH_Allocation_r16__numberOfRepetitions_r16__n1
 | PUSCH_Allocation_r16__numberOfRepetitions_r16__n2
 | PUSCH_Allocation_r16__numberOfRepetitions_r16__n3
 | PUSCH_Allocation_r16__numberOfRepetitions_r16__n4
 | PUSCH_Allocation_r16__numberOfRepetitions_r16__n7
 | PUSCH_Allocation_r16__numberOfRepetitions_r16__n8
 | PUSCH_Allocation_r16__numberOfRepetitions_r16__n12
 | PUSCH_Allocation_r16__numberOfRepetitions_r16__n16
.
Definition PUSCH_Allocation_r16__numberOfRepetitions_r16__cond := (fun (_ : PUSCH_Allocation_r16__numberOfRepetitions_r16__Type) => True).
Lemma PUSCH_Allocation_r16__numberOfRepetitions_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Allocation_r16__numberOfRepetitions_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PUSCH_Allocation_r16__numberOfRepetitions_r16__nat__helper.

Definition PUSCH_Allocation_r16__numberOfRepetitions_r16__F1 t :=
  match t with
  | PUSCH_Allocation_r16__numberOfRepetitions_r16__n1 => 0
  | PUSCH_Allocation_r16__numberOfRepetitions_r16__n2 => 1
  | PUSCH_Allocation_r16__numberOfRepetitions_r16__n3 => 2
  | PUSCH_Allocation_r16__numberOfRepetitions_r16__n4 => 3
  | PUSCH_Allocation_r16__numberOfRepetitions_r16__n7 => 4
  | PUSCH_Allocation_r16__numberOfRepetitions_r16__n8 => 5
  | PUSCH_Allocation_r16__numberOfRepetitions_r16__n12 => 6
  | PUSCH_Allocation_r16__numberOfRepetitions_r16__n16 => 7
  end.
Definition PUSCH_Allocation_r16__numberOfRepetitions_r16__F2 n :=
  match n with
  | 0 => PUSCH_Allocation_r16__numberOfRepetitions_r16__n1
  | 1 => PUSCH_Allocation_r16__numberOfRepetitions_r16__n2
  | 2 => PUSCH_Allocation_r16__numberOfRepetitions_r16__n3
  | 3 => PUSCH_Allocation_r16__numberOfRepetitions_r16__n4
  | 4 => PUSCH_Allocation_r16__numberOfRepetitions_r16__n7
  | 5 => PUSCH_Allocation_r16__numberOfRepetitions_r16__n8
  | 6 => PUSCH_Allocation_r16__numberOfRepetitions_r16__n12
  | 7 => PUSCH_Allocation_r16__numberOfRepetitions_r16__n16
  | _ => PUSCH_Allocation_r16__numberOfRepetitions_r16__n1
  end.
Lemma PUSCH_Allocation_r16__numberOfRepetitions_r16__F1F2 : forall x : PUSCH_Allocation_r16__numberOfRepetitions_r16__Type, (PUSCH_Allocation_r16__numberOfRepetitions_r16__F1 x <= 7) /\ PUSCH_Allocation_r16__numberOfRepetitions_r16__F2 (PUSCH_Allocation_r16__numberOfRepetitions_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Allocation_r16__numberOfRepetitions_r16__F2F1 : forall (y : nat) (H : y <= 7), PUSCH_Allocation_r16__numberOfRepetitions_r16__F1 (PUSCH_Allocation_r16__numberOfRepetitions_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Type : Set :=
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n1
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n2
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n3
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n4
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n7
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n8
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n12
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n16
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n20
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n24
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n28
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n32
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare4
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare3
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare2
 | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare1
.
Definition PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__cond := (fun (_ : PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Type) => True).
Lemma PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__nat__helper.

Definition PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F1 t :=
  match t with
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n1 => 0
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n2 => 1
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n3 => 2
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n4 => 3
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n7 => 4
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n8 => 5
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n12 => 6
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n16 => 7
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n20 => 8
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n24 => 9
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n28 => 10
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n32 => 11
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare4 => 12
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare3 => 13
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare2 => 14
  | PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare1 => 15
  end.
Definition PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F2 n :=
  match n with
  | 0 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n1
  | 1 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n2
  | 2 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n3
  | 3 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n4
  | 4 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n7
  | 5 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n8
  | 6 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n12
  | 7 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n16
  | 8 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n20
  | 9 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n24
  | 10 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n28
  | 11 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n32
  | 12 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare4
  | 13 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare3
  | 14 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare2
  | 15 => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__spare1
  | _ => PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__n1
  end.
Lemma PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F1F2 : forall x : PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Type, (PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F1 x <= 15) /\ PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F2 (PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F2F1 : forall (y : nat) (H : y <= 15), PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F1 (PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Type : Set :=
 | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n1
 | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n2
 | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n4
 | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n8
 | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare4
 | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare3
 | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare2
 | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare1
.
Definition PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__cond := (fun (_ : PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Type) => True).
Lemma PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__nat__helper.

Definition PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F1 t :=
  match t with
  | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n1 => 0
  | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n2 => 1
  | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n4 => 2
  | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n8 => 3
  | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare4 => 4
  | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare3 => 5
  | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare2 => 6
  | PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare1 => 7
  end.
Definition PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F2 n :=
  match n with
  | 0 => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n1
  | 1 => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n2
  | 2 => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n4
  | 3 => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n8
  | 4 => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare4
  | 5 => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare3
  | 6 => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare2
  | 7 => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__spare1
  | _ => PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__n1
  end.
Lemma PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F1F2 : forall x : PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Type, (PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F1 x <= 7) /\ PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F2 (PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F2F1 : forall (y : nat) (H : y <= 7), PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F1 (PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_Allocation_r16__ext0O__extendedK2_r17__helper1 : (0 <= 128)%Z.  lia. Qed.
Lemma PUSCH_Allocation_r16__ext0O__extendedK2_r17__helper2 : to_bit_sz (Z.to_nat (128 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Allocation_r16__ext0O__extendedK2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Allocation_r16__ext0O__extendedK2_r17__Type := Z.
Definition PUSCH_Allocation_r16__ext0O__extendedK2_r17__cond := (fun z => (0 <= z <= 128)%Z).
Record PUSCH_Allocation_r16__ext0O__Type : Set :=
  make__PUSCH_Allocation_r16__ext0O__Type {
    PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17 : option PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Type ;
    PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17 : option PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Type ;
    PUSCH_Allocation_r16__ext0O__extendedK2_r17 : option Z ;
}.
Definition PUSCH_Allocation_r16__ext0O__list := (
 Opt PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Type PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__cond ::
 Opt PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Type PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__cond ::
 Opt Z PUSCH_Allocation_r16__ext0O__extendedK2_r17__cond ::
 nil).
Definition PUSCH_Allocation_r16__ext0O__cond z := 
  opt_cond PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__cond (PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17 z) /\
  opt_cond PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__cond (PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17 z) /\
  opt_cond PUSCH_Allocation_r16__ext0O__extendedK2_r17__cond (PUSCH_Allocation_r16__ext0O__extendedK2_r17 z) /\
  True.

Definition PUSCH_Allocation_r16__ext0__Type := PUSCH_Allocation_r16__ext0O__Type.
Definition PUSCH_Allocation_r16__ext0__cond := PUSCH_Allocation_r16__ext0O__cond.

Record PUSCH_Allocation_r16__Type : Set :=
  make__PUSCH_Allocation_r16__Type {
    PUSCH_Allocation_r16__mappingType_r16 : option PUSCH_Allocation_r16__mappingType_r16__Type ;
    PUSCH_Allocation_r16__startSymbolAndLength_r16 : option Z ;
    PUSCH_Allocation_r16__startSymbol_r16 : option Z ;
    PUSCH_Allocation_r16__length_r16 : option Z ;
    PUSCH_Allocation_r16__numberOfRepetitions_r16 : option PUSCH_Allocation_r16__numberOfRepetitions_r16__Type ;
    PUSCH_Allocation_r16__ext0 : option PUSCH_Allocation_r16__ext0__Type ;
}.
Definition PUSCH_Allocation_r16__root_list : list seq_elem := (
 Opt PUSCH_Allocation_r16__mappingType_r16__Type PUSCH_Allocation_r16__mappingType_r16__cond ::
 Opt Z PUSCH_Allocation_r16__startSymbolAndLength_r16__cond ::
 Opt Z PUSCH_Allocation_r16__startSymbol_r16__cond ::
 Opt Z PUSCH_Allocation_r16__length_r16__cond ::
 Opt PUSCH_Allocation_r16__numberOfRepetitions_r16__Type PUSCH_Allocation_r16__numberOfRepetitions_r16__cond ::
 nil).
Definition PUSCH_Allocation_r16__ext_list : list typ := (
  typ_cons PUSCH_Allocation_r16__ext0__Type PUSCH_Allocation_r16__ext0__cond ::
  nil).
Definition PUSCH_Allocation_r16__cond (z : PUSCH_Allocation_r16__Type) := 
(  opt_cond PUSCH_Allocation_r16__mappingType_r16__cond (PUSCH_Allocation_r16__mappingType_r16 z) /\
  opt_cond PUSCH_Allocation_r16__startSymbolAndLength_r16__cond (PUSCH_Allocation_r16__startSymbolAndLength_r16 z) /\
  opt_cond PUSCH_Allocation_r16__startSymbol_r16__cond (PUSCH_Allocation_r16__startSymbol_r16 z) /\
  opt_cond PUSCH_Allocation_r16__length_r16__cond (PUSCH_Allocation_r16__length_r16 z) /\
  opt_cond PUSCH_Allocation_r16__numberOfRepetitions_r16__cond (PUSCH_Allocation_r16__numberOfRepetitions_r16 z) /\
  True) /\ 
(  opt_cond PUSCH_Allocation_r16__ext0__cond (PUSCH_Allocation_r16__ext0 z) /\
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
Definition PUSCH_Allocation_r16__mappingType_r16__Format : T_Format PUSCH_Allocation_r16__mappingType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Allocation_r16__mappingType_r16__nat__Format PUSCH_Allocation_r16__mappingType_r16__F1 PUSCH_Allocation_r16__mappingType_r16__F2 PUSCH_Allocation_r16__mappingType_r16__F1F2 PUSCH_Allocation_r16__mappingType_r16__F2F1.

Opaque PUSCH_Allocation_r16__mappingType_r16__cond PUSCH_Allocation_r16__mappingType_r16__Format.

Definition PUSCH_Allocation_r16__startSymbolAndLength_r16__Format : T_Format Z PUSCH_Allocation_r16__startSymbolAndLength_r16__cond :=
 ranged_int_format (0) (127) PUSCH_Allocation_r16__startSymbolAndLength_r16__helper1 PUSCH_Allocation_r16__startSymbolAndLength_r16__helper2.

Opaque PUSCH_Allocation_r16__startSymbolAndLength_r16__cond PUSCH_Allocation_r16__startSymbolAndLength_r16__Format.

Definition PUSCH_Allocation_r16__startSymbol_r16__Format : T_Format Z PUSCH_Allocation_r16__startSymbol_r16__cond :=
 ranged_int_format (0) (13) PUSCH_Allocation_r16__startSymbol_r16__helper1 PUSCH_Allocation_r16__startSymbol_r16__helper2.

Opaque PUSCH_Allocation_r16__startSymbol_r16__cond PUSCH_Allocation_r16__startSymbol_r16__Format.

Definition PUSCH_Allocation_r16__length_r16__Format : T_Format Z PUSCH_Allocation_r16__length_r16__cond :=
 ranged_int_format (1) (14) PUSCH_Allocation_r16__length_r16__helper1 PUSCH_Allocation_r16__length_r16__helper2.

Opaque PUSCH_Allocation_r16__length_r16__cond PUSCH_Allocation_r16__length_r16__Format.

Definition PUSCH_Allocation_r16__numberOfRepetitions_r16__Format : T_Format PUSCH_Allocation_r16__numberOfRepetitions_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Allocation_r16__numberOfRepetitions_r16__nat__Format PUSCH_Allocation_r16__numberOfRepetitions_r16__F1 PUSCH_Allocation_r16__numberOfRepetitions_r16__F2 PUSCH_Allocation_r16__numberOfRepetitions_r16__F1F2 PUSCH_Allocation_r16__numberOfRepetitions_r16__F2F1.

Opaque PUSCH_Allocation_r16__numberOfRepetitions_r16__cond PUSCH_Allocation_r16__numberOfRepetitions_r16__Format.

Definition PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Format : T_Format PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__nat__Format PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F1 PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F2 PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F1F2 PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__F2F1.

Opaque PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__cond PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Format.

Definition PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Format : T_Format PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__nat__Format PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F1 PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F2 PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F1F2 PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__F2F1.

Opaque PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__cond PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Format.

Definition PUSCH_Allocation_r16__ext0O__extendedK2_r17__Format : T_Format Z PUSCH_Allocation_r16__ext0O__extendedK2_r17__cond :=
 ranged_int_format (0) (128) PUSCH_Allocation_r16__ext0O__extendedK2_r17__helper1 PUSCH_Allocation_r16__ext0O__extendedK2_r17__helper2.

Opaque PUSCH_Allocation_r16__ext0O__extendedK2_r17__cond PUSCH_Allocation_r16__ext0O__extendedK2_r17__Format.


Definition PUSCH_Allocation_r16__ext0O__Format_Type := Eval cbn in seq_format_prod PUSCH_Allocation_r16__ext0O__list.
Definition PUSCH_Allocation_r16__ext0O__Format_list : PUSCH_Allocation_r16__ext0O__Format_Type :=
  (PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17__Format, (PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17__Format, (PUSCH_Allocation_r16__ext0O__extendedK2_r17__Format, unit_format))).
Definition PUSCH_Allocation_r16__ext0O__list__Format := (*Eval compute in *) seq_format PUSCH_Allocation_r16__ext0O__list PUSCH_Allocation_r16__ext0O__Format_list.
Definition PUSCH_Allocation_r16__ext0O__F1 z :=
  (PUSCH_Allocation_r16__ext0O__numberOfRepetitionsExt_r17 z, (PUSCH_Allocation_r16__ext0O__numberOfSlotsTBoMS_r17 z, (PUSCH_Allocation_r16__ext0O__extendedK2_r17 z, tt))).
Definition PUSCH_Allocation_r16__ext0O__F2 (y : seq_type PUSCH_Allocation_r16__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PUSCH_Allocation_r16__ext0O__Type i0 i1 i2
  end.
Lemma PUSCH_Allocation_r16__ext0O__F1F2_cond (z : PUSCH_Allocation_r16__ext0O__Type)
  : PUSCH_Allocation_r16__ext0O__cond z ->
  (seq_cond PUSCH_Allocation_r16__ext0O__list (PUSCH_Allocation_r16__ext0O__F1 z)).
intro H. unfold PUSCH_Allocation_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma PUSCH_Allocation_r16__ext0O__F1F2_cond2 (z : PUSCH_Allocation_r16__ext0O__Type)
 : PUSCH_Allocation_r16__ext0O__F2 (PUSCH_Allocation_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_Allocation_r16__ext0O__F2F1_cond (y : seq_type PUSCH_Allocation_r16__ext0O__list)
  : seq_cond PUSCH_Allocation_r16__ext0O__list y ->
 (PUSCH_Allocation_r16__ext0O__cond (PUSCH_Allocation_r16__ext0O__F2 y)) /\  PUSCH_Allocation_r16__ext0O__F1 (PUSCH_Allocation_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_Allocation_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUSCH_Allocation_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_Allocation_r16__ext0O__Format : T_Format PUSCH_Allocation_r16__ext0O__Type PUSCH_Allocation_r16__ext0O__cond :=
        proj2_format  PUSCH_Allocation_r16__ext0O__cond PUSCH_Allocation_r16__ext0O__list__Format
    PUSCH_Allocation_r16__ext0O__F1 PUSCH_Allocation_r16__ext0O__F2 PUSCH_Allocation_r16__ext0O__F1F2_cond  PUSCH_Allocation_r16__ext0O__F1F2_cond2 PUSCH_Allocation_r16__ext0O__F2F1_cond.
Opaque PUSCH_Allocation_r16__ext0O__cond PUSCH_Allocation_r16__ext0O__Format.

Definition PUSCH_Allocation_r16__ext0__check_all_none (b : PUSCH_Allocation_r16__ext0O__Type) : bool :=
match b with 
  | make__PUSCH_Allocation_r16__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition PUSCH_Allocation_r16__ext0__Format : T_Format PUSCH_Allocation_r16__ext0__Type PUSCH_Allocation_r16__ext0__cond :=
  restrict_add_format PUSCH_Allocation_r16__ext0__check_all_none PUSCH_Allocation_r16__ext0O__Format.

Opaque PUSCH_Allocation_r16__ext0__cond PUSCH_Allocation_r16__ext0__Format.


Definition PUSCH_Allocation_r16__root_Format_Type := Eval cbn in seq_format_prod PUSCH_Allocation_r16__root_list.
Definition PUSCH_Allocation_r16__root_Format_list : PUSCH_Allocation_r16__root_Format_Type :=
  (PUSCH_Allocation_r16__mappingType_r16__Format, (PUSCH_Allocation_r16__startSymbolAndLength_r16__Format, (PUSCH_Allocation_r16__startSymbol_r16__Format, (PUSCH_Allocation_r16__length_r16__Format, (PUSCH_Allocation_r16__numberOfRepetitions_r16__Format, unit_format))))).

Definition PUSCH_Allocation_r16__ext_Format_Type := Eval cbn in get_formats PUSCH_Allocation_r16__ext_list.
Definition PUSCH_Allocation_r16__ext_Format_list : PUSCH_Allocation_r16__ext_Format_Type :=
  (PUSCH_Allocation_r16__ext0__Format, unit__Format).

Definition PUSCH_Allocation_r16__list_type : Set := (seq_type PUSCH_Allocation_r16__root_list) * (seq_ext_type PUSCH_Allocation_r16__ext_list).
Definition PUSCH_Allocation_r16__list_cond (z : PUSCH_Allocation_r16__list_type) : Prop :=
        (seq_cond PUSCH_Allocation_r16__root_list (fst z)) /\ (seq_ext_cond PUSCH_Allocation_r16__ext_list (snd z)).
Definition PUSCH_Allocation_r16__list_format : T_Format PUSCH_Allocation_r16__list_type PUSCH_Allocation_r16__list_cond :=
 (* Eval compute in *) seq_ext_format PUSCH_Allocation_r16__root_list PUSCH_Allocation_r16__root_Format_list PUSCH_Allocation_r16__ext_list PUSCH_Allocation_r16__ext_Format_list.

Opaque PUSCH_Allocation_r16__list_format.
Definition PUSCH_Allocation_r16__F1 (z : PUSCH_Allocation_r16__Type) : PUSCH_Allocation_r16__list_type :=
  (((PUSCH_Allocation_r16__mappingType_r16 z, (PUSCH_Allocation_r16__startSymbolAndLength_r16 z, (PUSCH_Allocation_r16__startSymbol_r16 z, (PUSCH_Allocation_r16__length_r16 z, (PUSCH_Allocation_r16__numberOfRepetitions_r16 z, tt)))))), (
(PUSCH_Allocation_r16__ext0 z, tt))).
Definition PUSCH_Allocation_r16__F2 (y : PUSCH_Allocation_r16__list_type) : PUSCH_Allocation_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, _))=>
    make__PUSCH_Allocation_r16__Type j0 j1 j2 j3 j4 i0
  end.
Definition PUSCH_Allocation_r16__helper1 : (forall a : PUSCH_Allocation_r16__Type, PUSCH_Allocation_r16__cond a -> PUSCH_Allocation_r16__list_cond (PUSCH_Allocation_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUSCH_Allocation_r16__helper2 : (forall a : PUSCH_Allocation_r16__Type, PUSCH_Allocation_r16__F2 (PUSCH_Allocation_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUSCH_Allocation_r16__helper3 : (forall b : PUSCH_Allocation_r16__list_type, PUSCH_Allocation_r16__list_cond b -> PUSCH_Allocation_r16__cond (PUSCH_Allocation_r16__F2 b) /\ PUSCH_Allocation_r16__F1 (PUSCH_Allocation_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUSCH_Allocation_r16__cond, PUSCH_Allocation_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUSCH_Allocation_r16__Format : T_Format PUSCH_Allocation_r16__Type PUSCH_Allocation_r16__cond :=
 proj2_format PUSCH_Allocation_r16__cond PUSCH_Allocation_r16__list_format  PUSCH_Allocation_r16__F1 PUSCH_Allocation_r16__F2 PUSCH_Allocation_r16__helper1 PUSCH_Allocation_r16__helper2 PUSCH_Allocation_r16__helper3.

Opaque PUSCH_Allocation_r16__cond PUSCH_Allocation_r16__Format.

