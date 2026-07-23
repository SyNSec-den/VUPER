Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive TRS_ResourceSet_r17__powerControlOffsetSS_r17__Type : Set :=
 | TRS_ResourceSet_r17__powerControlOffsetSS_r17__db_3
 | TRS_ResourceSet_r17__powerControlOffsetSS_r17__db0
 | TRS_ResourceSet_r17__powerControlOffsetSS_r17__db3
 | TRS_ResourceSet_r17__powerControlOffsetSS_r17__db6
.
Definition TRS_ResourceSet_r17__powerControlOffsetSS_r17__cond := (fun (_ : TRS_ResourceSet_r17__powerControlOffsetSS_r17__Type) => True).
Lemma TRS_ResourceSet_r17__powerControlOffsetSS_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition TRS_ResourceSet_r17__powerControlOffsetSS_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 TRS_ResourceSet_r17__powerControlOffsetSS_r17__nat__helper.

Definition TRS_ResourceSet_r17__powerControlOffsetSS_r17__F1 t :=
  match t with
  | TRS_ResourceSet_r17__powerControlOffsetSS_r17__db_3 => 0
  | TRS_ResourceSet_r17__powerControlOffsetSS_r17__db0 => 1
  | TRS_ResourceSet_r17__powerControlOffsetSS_r17__db3 => 2
  | TRS_ResourceSet_r17__powerControlOffsetSS_r17__db6 => 3
  end.
Definition TRS_ResourceSet_r17__powerControlOffsetSS_r17__F2 n :=
  match n with
  | 0 => TRS_ResourceSet_r17__powerControlOffsetSS_r17__db_3
  | 1 => TRS_ResourceSet_r17__powerControlOffsetSS_r17__db0
  | 2 => TRS_ResourceSet_r17__powerControlOffsetSS_r17__db3
  | 3 => TRS_ResourceSet_r17__powerControlOffsetSS_r17__db6
  | _ => TRS_ResourceSet_r17__powerControlOffsetSS_r17__db_3
  end.
Lemma TRS_ResourceSet_r17__powerControlOffsetSS_r17__F1F2 : forall x : TRS_ResourceSet_r17__powerControlOffsetSS_r17__Type, (TRS_ResourceSet_r17__powerControlOffsetSS_r17__F1 x <= 3) /\ TRS_ResourceSet_r17__powerControlOffsetSS_r17__F2 (TRS_ResourceSet_r17__powerControlOffsetSS_r17__F1 x) = x. imp_solve. Qed.
Lemma TRS_ResourceSet_r17__powerControlOffsetSS_r17__F2F1 : forall (y : nat) (H : y <= 3), TRS_ResourceSet_r17__powerControlOffsetSS_r17__F1 (TRS_ResourceSet_r17__powerControlOffsetSS_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ScramblingId.

Opaque ScramblingId__cond ScramblingId__Format.

Require Import NR.ScramblingId.

Opaque ScramblingId__cond ScramblingId__Format.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Type := list ScramblingId__Type.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__cond (z : TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Type) := (list_and ScramblingId__cond z) /\ (length z = Z.to_nat 2).

Require Import NR.ScramblingId.

Opaque ScramblingId__cond ScramblingId__Format.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Type := list ScramblingId__Type.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__cond (z : TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Type) := (list_and ScramblingId__cond z) /\ (length z = Z.to_nat 4).


Inductive TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type : Set :=
  | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDforCommon_r17 : ScramblingId__Type -> TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type
  | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17 : TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Type -> TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type
  | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17 : TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Type -> TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type
.
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__list : list typ := (
typ_cons ScramblingId__Type ScramblingId__cond ::
typ_cons TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Type TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__cond ::
typ_cons TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Type TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__cond ::
 nil).
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__cond (c : TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type) := 
  match c with
  | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDforCommon_r17 t => ScramblingId__cond t 
  | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17 t => TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__cond t 
  | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17 t => TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__cond t 
  end.

Lemma TRS_ResourceSet_r17__scramblingID_Info_r17__root__len_helper1 : to_bit_sz (length TRS_ResourceSet_r17__scramblingID_Info_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma TRS_ResourceSet_r17__scramblingID_Info_r17__root__len_helper2 : 2 <= length2 TRS_ResourceSet_r17__scramblingID_Info_r17__root__list.
 simpl. lia. Qed.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__ext__Type : Set := Empty_set.
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__ext__cond (c : TRS_ResourceSet_r17__scramblingID_Info_r17__ext__Type) := True.
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__Type : Set := TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type + TRS_ResourceSet_r17__scramblingID_Info_r17__ext__Type.
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__cond :=
  sum_cond TRS_ResourceSet_r17__scramblingID_Info_r17__root__cond TRS_ResourceSet_r17__scramblingID_Info_r17__ext__cond.
Lemma TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__Type := Z.
Definition TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__cond := (fun z => (0 <= z <= 9)%Z).
Lemma TRS_ResourceSet_r17__startingRB_r17__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma TRS_ResourceSet_r17__startingRB_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TRS_ResourceSet_r17__startingRB_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TRS_ResourceSet_r17__startingRB_r17__Type := Z.
Definition TRS_ResourceSet_r17__startingRB_r17__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Lemma TRS_ResourceSet_r17__nrofRBs_r17__helper1 : (24 <= maxNrofPhysicalResourceBlocksPlus1)%Z. unfold maxNrofPhysicalResourceBlocksPlus1.
 lia. Qed.
Lemma TRS_ResourceSet_r17__nrofRBs_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocksPlus1 - 24)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocksPlus1 - 24))%Z). { apply Zorder.Zle_minus_le_0. apply TRS_ResourceSet_r17__nrofRBs_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TRS_ResourceSet_r17__nrofRBs_r17__Type := Z.
Definition TRS_ResourceSet_r17__nrofRBs_r17__cond := (fun z => (24 <= z <= maxNrofPhysicalResourceBlocksPlus1)%Z).
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__Type := Z.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__Type := Z.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__Type := Z.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__Type := Z.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__cond := (fun z => (0 <= z <= 79)%Z).

Inductive TRS_ResourceSet_r17__periodicityAndOffset_r17__Type : Set :=
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10 : Z -> TRS_ResourceSet_r17__periodicityAndOffset_r17__Type
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20 : Z -> TRS_ResourceSet_r17__periodicityAndOffset_r17__Type
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40 : Z -> TRS_ResourceSet_r17__periodicityAndOffset_r17__Type
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80 : Z -> TRS_ResourceSet_r17__periodicityAndOffset_r17__Type
.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__list : list typ := (
typ_cons Z TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__cond ::
typ_cons Z TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__cond ::
typ_cons Z TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__cond ::
typ_cons Z TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__cond ::
 nil).
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__cond (c : TRS_ResourceSet_r17__periodicityAndOffset_r17__Type) := 
  match c with
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10 t => TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__cond t 
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20 t => TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__cond t 
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40 t => TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__cond t 
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80 t => TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__cond t 
  end.

Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__len_helper1 : to_bit_sz (length TRS_ResourceSet_r17__periodicityAndOffset_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__len_helper2 : 2 <= length2 TRS_ResourceSet_r17__periodicityAndOffset_r17__list.
 simpl. lia. Qed.
Definition TRS_ResourceSet_r17__frequencyDomainAllocation_r17__Type := bit_string_fixed.
Definition TRS_ResourceSet_r17__frequencyDomainAllocation_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Lemma TRS_ResourceSet_r17__indBitID_r17__helper1 : (0 <= 5)%Z.  lia. Qed.
Lemma TRS_ResourceSet_r17__indBitID_r17__helper2 : to_bit_sz (Z.to_nat (5 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply TRS_ResourceSet_r17__indBitID_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition TRS_ResourceSet_r17__indBitID_r17__Type := Z.
Definition TRS_ResourceSet_r17__indBitID_r17__cond := (fun z => (0 <= z <= 5)%Z).
Inductive TRS_ResourceSet_r17__nrofResources_r17__Type : Set :=
 | TRS_ResourceSet_r17__nrofResources_r17__n2
 | TRS_ResourceSet_r17__nrofResources_r17__n4
.
Definition TRS_ResourceSet_r17__nrofResources_r17__cond := (fun (_ : TRS_ResourceSet_r17__nrofResources_r17__Type) => True).
Lemma TRS_ResourceSet_r17__nrofResources_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition TRS_ResourceSet_r17__nrofResources_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 TRS_ResourceSet_r17__nrofResources_r17__nat__helper.

Definition TRS_ResourceSet_r17__nrofResources_r17__F1 t :=
  match t with
  | TRS_ResourceSet_r17__nrofResources_r17__n2 => 0
  | TRS_ResourceSet_r17__nrofResources_r17__n4 => 1
  end.
Definition TRS_ResourceSet_r17__nrofResources_r17__F2 n :=
  match n with
  | 0 => TRS_ResourceSet_r17__nrofResources_r17__n2
  | 1 => TRS_ResourceSet_r17__nrofResources_r17__n4
  | _ => TRS_ResourceSet_r17__nrofResources_r17__n2
  end.
Lemma TRS_ResourceSet_r17__nrofResources_r17__F1F2 : forall x : TRS_ResourceSet_r17__nrofResources_r17__Type, (TRS_ResourceSet_r17__nrofResources_r17__F1 x <= 1) /\ TRS_ResourceSet_r17__nrofResources_r17__F2 (TRS_ResourceSet_r17__nrofResources_r17__F1 x) = x. imp_solve. Qed.
Lemma TRS_ResourceSet_r17__nrofResources_r17__F2F1 : forall (y : nat) (H : y <= 1), TRS_ResourceSet_r17__nrofResources_r17__F1 (TRS_ResourceSet_r17__nrofResources_r17__F2 y) = y. enum_solve H y. Qed.

Record TRS_ResourceSet_r17__Type : Set :=
  make__TRS_ResourceSet_r17__Type {
    TRS_ResourceSet_r17__powerControlOffsetSS_r17 : TRS_ResourceSet_r17__powerControlOffsetSS_r17__Type ;
    TRS_ResourceSet_r17__scramblingID_Info_r17 : TRS_ResourceSet_r17__scramblingID_Info_r17__Type ;
    TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17 : Z ;
    TRS_ResourceSet_r17__startingRB_r17 : Z ;
    TRS_ResourceSet_r17__nrofRBs_r17 : Z ;
    TRS_ResourceSet_r17__ssb_Index_r17 : SSB_Index__Type ;
    TRS_ResourceSet_r17__periodicityAndOffset_r17 : TRS_ResourceSet_r17__periodicityAndOffset_r17__Type ;
    TRS_ResourceSet_r17__frequencyDomainAllocation_r17 : TRS_ResourceSet_r17__frequencyDomainAllocation_r17__Type ;
    TRS_ResourceSet_r17__indBitID_r17 : Z ;
    TRS_ResourceSet_r17__nrofResources_r17 : TRS_ResourceSet_r17__nrofResources_r17__Type ;
}.
Definition TRS_ResourceSet_r17__list := (
 Nor TRS_ResourceSet_r17__powerControlOffsetSS_r17__Type TRS_ResourceSet_r17__powerControlOffsetSS_r17__cond ::
 Nor TRS_ResourceSet_r17__scramblingID_Info_r17__Type TRS_ResourceSet_r17__scramblingID_Info_r17__cond ::
 Nor Z TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__cond ::
 Nor Z TRS_ResourceSet_r17__startingRB_r17__cond ::
 Nor Z TRS_ResourceSet_r17__nrofRBs_r17__cond ::
 Nor SSB_Index__Type SSB_Index__cond ::
 Nor TRS_ResourceSet_r17__periodicityAndOffset_r17__Type TRS_ResourceSet_r17__periodicityAndOffset_r17__cond ::
 Nor TRS_ResourceSet_r17__frequencyDomainAllocation_r17__Type TRS_ResourceSet_r17__frequencyDomainAllocation_r17__cond ::
 Nor Z TRS_ResourceSet_r17__indBitID_r17__cond ::
 Nor TRS_ResourceSet_r17__nrofResources_r17__Type TRS_ResourceSet_r17__nrofResources_r17__cond ::
 nil).
Definition TRS_ResourceSet_r17__cond z := 
  TRS_ResourceSet_r17__powerControlOffsetSS_r17__cond (TRS_ResourceSet_r17__powerControlOffsetSS_r17 z) /\
  TRS_ResourceSet_r17__scramblingID_Info_r17__cond (TRS_ResourceSet_r17__scramblingID_Info_r17 z) /\
  TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__cond (TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17 z) /\
  TRS_ResourceSet_r17__startingRB_r17__cond (TRS_ResourceSet_r17__startingRB_r17 z) /\
  TRS_ResourceSet_r17__nrofRBs_r17__cond (TRS_ResourceSet_r17__nrofRBs_r17 z) /\
  SSB_Index__cond (TRS_ResourceSet_r17__ssb_Index_r17 z) /\
  TRS_ResourceSet_r17__periodicityAndOffset_r17__cond (TRS_ResourceSet_r17__periodicityAndOffset_r17 z) /\
  TRS_ResourceSet_r17__frequencyDomainAllocation_r17__cond (TRS_ResourceSet_r17__frequencyDomainAllocation_r17 z) /\
  TRS_ResourceSet_r17__indBitID_r17__cond (TRS_ResourceSet_r17__indBitID_r17 z) /\
  TRS_ResourceSet_r17__nrofResources_r17__cond (TRS_ResourceSet_r17__nrofResources_r17 z) /\
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
Definition TRS_ResourceSet_r17__powerControlOffsetSS_r17__Format : T_Format TRS_ResourceSet_r17__powerControlOffsetSS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format TRS_ResourceSet_r17__powerControlOffsetSS_r17__nat__Format TRS_ResourceSet_r17__powerControlOffsetSS_r17__F1 TRS_ResourceSet_r17__powerControlOffsetSS_r17__F2 TRS_ResourceSet_r17__powerControlOffsetSS_r17__F1F2 TRS_ResourceSet_r17__powerControlOffsetSS_r17__F2F1.

Opaque TRS_ResourceSet_r17__powerControlOffsetSS_r17__cond TRS_ResourceSet_r17__powerControlOffsetSS_r17__Format.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Format : T_Format TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Type TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__cond := seq_of_fixed_format ScramblingId__Format 2.

Opaque TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__cond TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Format.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Format : T_Format TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Type TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__cond := seq_of_fixed_format ScramblingId__Format 4.

Opaque TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__cond TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Format.


Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__Format_Type := Eval cbn in get_formats TRS_ResourceSet_r17__scramblingID_Info_r17__root__list.
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__Format_list : TRS_ResourceSet_r17__scramblingID_Info_r17__root__Format_Type :=
  (ScramblingId__Format, (TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Format, (TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Format, unit__Format))).
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__list__Format := Eval compute in choice_format TRS_ResourceSet_r17__scramblingID_Info_r17__root__list TRS_ResourceSet_r17__scramblingID_Info_r17__root__len_helper1 TRS_ResourceSet_r17__scramblingID_Info_r17__root__len_helper2  TRS_ResourceSet_r17__scramblingID_Info_r17__root__Format_list.
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__F1 (z : TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type) : (choice TRS_ResourceSet_r17__scramblingID_Info_r17__root__list) :=
  match z with
   | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDforCommon_r17 t => existT _ 0 t
  | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17 t => existT _ 1 t
  | TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17 t => existT _ 2 t
  end.
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__g := (fun n => typ_set (get_nth_typ TRS_ResourceSet_r17__scramblingID_Info_r17__root__list n)).
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__F2 (y : choice TRS_ResourceSet_r17__scramblingID_Info_r17__root__list) : TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (TRS_ResourceSet_r17__scramblingID_Info_r17__root__g n -> TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type) with
    | 0 => fun (t : ScramblingId__Type) => TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDforCommon_r17 t 
    | 1 => fun (t : TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17__Type) => TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith2_r17 t 
    | 2 => fun (t : TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17__Type) => TRS_ResourceSet_r17__scramblingID_Info_r17__root__scramblingIDperResourceListWith4_r17 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : TRS_ResourceSet_r17__scramblingID_Info_r17__root__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ TRS_ResourceSet_r17__scramblingID_Info_r17__root__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len TRS_ResourceSet_r17__scramblingID_Info_r17__root__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type with end) n0
           end t0).

Lemma TRS_ResourceSet_r17__scramblingID_Info_r17__root__helper2 :  forall (y : TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type), TRS_ResourceSet_r17__scramblingID_Info_r17__root__cond y -> choice_cond TRS_ResourceSet_r17__scramblingID_Info_r17__root__list (TRS_ResourceSet_r17__scramblingID_Info_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma TRS_ResourceSet_r17__scramblingID_Info_r17__root__helper3 :  forall (y : TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type), TRS_ResourceSet_r17__scramblingID_Info_r17__root__F2 (TRS_ResourceSet_r17__scramblingID_Info_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma TRS_ResourceSet_r17__scramblingID_Info_r17__root__helper4 : (forall b : choice TRS_ResourceSet_r17__scramblingID_Info_r17__root__list, choice_cond TRS_ResourceSet_r17__scramblingID_Info_r17__root__list b -> TRS_ResourceSet_r17__scramblingID_Info_r17__root__cond (TRS_ResourceSet_r17__scramblingID_Info_r17__root__F2 b) /\ TRS_ResourceSet_r17__scramblingID_Info_r17__root__F1 (TRS_ResourceSet_r17__scramblingID_Info_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length TRS_ResourceSet_r17__scramblingID_Info_r17__root__F1 TRS_ResourceSet_r17__scramblingID_Info_r17__root__F2.
Definition TRS_ResourceSet_r17__scramblingID_Info_r17__root__Format : T_Format TRS_ResourceSet_r17__scramblingID_Info_r17__root__Type TRS_ResourceSet_r17__scramblingID_Info_r17__root__cond :=
  (* Eval compute in *) proj2_format TRS_ResourceSet_r17__scramblingID_Info_r17__root__cond TRS_ResourceSet_r17__scramblingID_Info_r17__root__list__Format TRS_ResourceSet_r17__scramblingID_Info_r17__root__F1 TRS_ResourceSet_r17__scramblingID_Info_r17__root__F2 TRS_ResourceSet_r17__scramblingID_Info_r17__root__helper2 TRS_ResourceSet_r17__scramblingID_Info_r17__root__helper3 TRS_ResourceSet_r17__scramblingID_Info_r17__root__helper4.
Opaque TRS_ResourceSet_r17__scramblingID_Info_r17__root__cond TRS_ResourceSet_r17__scramblingID_Info_r17__root__Format.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__ext__Format : T_Format TRS_ResourceSet_r17__scramblingID_Info_r17__ext__Type TRS_ResourceSet_r17__scramblingID_Info_r17__ext__cond := empty_format.
Opaque TRS_ResourceSet_r17__scramblingID_Info_r17__ext__cond TRS_ResourceSet_r17__scramblingID_Info_r17__ext__Format.

Definition TRS_ResourceSet_r17__scramblingID_Info_r17__Format : T_Format TRS_ResourceSet_r17__scramblingID_Info_r17__Type TRS_ResourceSet_r17__scramblingID_Info_r17__cond := sum_format TRS_ResourceSet_r17__scramblingID_Info_r17__root__Format TRS_ResourceSet_r17__scramblingID_Info_r17__ext__Format.
Opaque TRS_ResourceSet_r17__scramblingID_Info_r17__cond TRS_ResourceSet_r17__scramblingID_Info_r17__Format.

Definition TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__Format : T_Format Z TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__cond :=
 ranged_int_format (0) (9) TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__helper1 TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__helper2.

Opaque TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__cond TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__Format.

Definition TRS_ResourceSet_r17__startingRB_r17__Format : T_Format Z TRS_ResourceSet_r17__startingRB_r17__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) TRS_ResourceSet_r17__startingRB_r17__helper1 TRS_ResourceSet_r17__startingRB_r17__helper2.

Opaque TRS_ResourceSet_r17__startingRB_r17__cond TRS_ResourceSet_r17__startingRB_r17__Format.

Definition TRS_ResourceSet_r17__nrofRBs_r17__Format : T_Format Z TRS_ResourceSet_r17__nrofRBs_r17__cond :=
 ranged_int_format (24) (maxNrofPhysicalResourceBlocksPlus1) TRS_ResourceSet_r17__nrofRBs_r17__helper1 TRS_ResourceSet_r17__nrofRBs_r17__helper2.

Opaque TRS_ResourceSet_r17__nrofRBs_r17__cond TRS_ResourceSet_r17__nrofRBs_r17__Format.

Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__Format : T_Format Z TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__cond :=
 ranged_int_format (0) (9) TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__helper1 TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__helper2.

Opaque TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__cond TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__Format.

Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__Format : T_Format Z TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__cond :=
 ranged_int_format (0) (19) TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__helper1 TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__helper2.

Opaque TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__cond TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__Format.

Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__Format : T_Format Z TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__cond :=
 ranged_int_format (0) (39) TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__helper1 TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__helper2.

Opaque TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__cond TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__Format.

Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__Format : T_Format Z TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__cond :=
 ranged_int_format (0) (79) TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__helper1 TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__helper2.

Opaque TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__cond TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__Format.


Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__Format_Type := Eval cbn in get_formats TRS_ResourceSet_r17__periodicityAndOffset_r17__list.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__Format_list : TRS_ResourceSet_r17__periodicityAndOffset_r17__Format_Type :=
  (TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10__Format, (TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20__Format, (TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40__Format, (TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80__Format, unit__Format)))).
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__list__Format := Eval compute in choice_format TRS_ResourceSet_r17__periodicityAndOffset_r17__list TRS_ResourceSet_r17__periodicityAndOffset_r17__len_helper1 TRS_ResourceSet_r17__periodicityAndOffset_r17__len_helper2  TRS_ResourceSet_r17__periodicityAndOffset_r17__Format_list.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__F1 (z : TRS_ResourceSet_r17__periodicityAndOffset_r17__Type) : (choice TRS_ResourceSet_r17__periodicityAndOffset_r17__list) :=
  match z with
   | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10 t => existT _ 0 t
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20 t => existT _ 1 t
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40 t => existT _ 2 t
  | TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80 t => existT _ 3 t
  end.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__g := (fun n => typ_set (get_nth_typ TRS_ResourceSet_r17__periodicityAndOffset_r17__list n)).
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__F2 (y : choice TRS_ResourceSet_r17__periodicityAndOffset_r17__list) : TRS_ResourceSet_r17__periodicityAndOffset_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (TRS_ResourceSet_r17__periodicityAndOffset_r17__g n -> TRS_ResourceSet_r17__periodicityAndOffset_r17__Type) with
    | 0 => fun (t : Z) => TRS_ResourceSet_r17__periodicityAndOffset_r17__slots10 t 
    | 1 => fun (t : Z) => TRS_ResourceSet_r17__periodicityAndOffset_r17__slots20 t 
    | 2 => fun (t : Z) => TRS_ResourceSet_r17__periodicityAndOffset_r17__slots40 t 
    | 3 => fun (t : Z) => TRS_ResourceSet_r17__periodicityAndOffset_r17__slots80 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : TRS_ResourceSet_r17__periodicityAndOffset_r17__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ TRS_ResourceSet_r17__periodicityAndOffset_r17__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len TRS_ResourceSet_r17__periodicityAndOffset_r17__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return TRS_ResourceSet_r17__periodicityAndOffset_r17__Type with end) n0
           end t0).

Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__helper2 :  forall (y : TRS_ResourceSet_r17__periodicityAndOffset_r17__Type), TRS_ResourceSet_r17__periodicityAndOffset_r17__cond y -> choice_cond TRS_ResourceSet_r17__periodicityAndOffset_r17__list (TRS_ResourceSet_r17__periodicityAndOffset_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__helper3 :  forall (y : TRS_ResourceSet_r17__periodicityAndOffset_r17__Type), TRS_ResourceSet_r17__periodicityAndOffset_r17__F2 (TRS_ResourceSet_r17__periodicityAndOffset_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma TRS_ResourceSet_r17__periodicityAndOffset_r17__helper4 : (forall b : choice TRS_ResourceSet_r17__periodicityAndOffset_r17__list, choice_cond TRS_ResourceSet_r17__periodicityAndOffset_r17__list b -> TRS_ResourceSet_r17__periodicityAndOffset_r17__cond (TRS_ResourceSet_r17__periodicityAndOffset_r17__F2 b) /\ TRS_ResourceSet_r17__periodicityAndOffset_r17__F1 (TRS_ResourceSet_r17__periodicityAndOffset_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length TRS_ResourceSet_r17__periodicityAndOffset_r17__F1 TRS_ResourceSet_r17__periodicityAndOffset_r17__F2.
Definition TRS_ResourceSet_r17__periodicityAndOffset_r17__Format : T_Format TRS_ResourceSet_r17__periodicityAndOffset_r17__Type TRS_ResourceSet_r17__periodicityAndOffset_r17__cond :=
  (* Eval compute in *) proj2_format TRS_ResourceSet_r17__periodicityAndOffset_r17__cond TRS_ResourceSet_r17__periodicityAndOffset_r17__list__Format TRS_ResourceSet_r17__periodicityAndOffset_r17__F1 TRS_ResourceSet_r17__periodicityAndOffset_r17__F2 TRS_ResourceSet_r17__periodicityAndOffset_r17__helper2 TRS_ResourceSet_r17__periodicityAndOffset_r17__helper3 TRS_ResourceSet_r17__periodicityAndOffset_r17__helper4.
Opaque TRS_ResourceSet_r17__periodicityAndOffset_r17__cond TRS_ResourceSet_r17__periodicityAndOffset_r17__Format.

Definition TRS_ResourceSet_r17__frequencyDomainAllocation_r17__Format : T_Format TRS_ResourceSet_r17__frequencyDomainAllocation_r17__Type TRS_ResourceSet_r17__frequencyDomainAllocation_r17__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque TRS_ResourceSet_r17__frequencyDomainAllocation_r17__cond TRS_ResourceSet_r17__frequencyDomainAllocation_r17__Format.

Definition TRS_ResourceSet_r17__indBitID_r17__Format : T_Format Z TRS_ResourceSet_r17__indBitID_r17__cond :=
 ranged_int_format (0) (5) TRS_ResourceSet_r17__indBitID_r17__helper1 TRS_ResourceSet_r17__indBitID_r17__helper2.

Opaque TRS_ResourceSet_r17__indBitID_r17__cond TRS_ResourceSet_r17__indBitID_r17__Format.

Definition TRS_ResourceSet_r17__nrofResources_r17__Format : T_Format TRS_ResourceSet_r17__nrofResources_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format TRS_ResourceSet_r17__nrofResources_r17__nat__Format TRS_ResourceSet_r17__nrofResources_r17__F1 TRS_ResourceSet_r17__nrofResources_r17__F2 TRS_ResourceSet_r17__nrofResources_r17__F1F2 TRS_ResourceSet_r17__nrofResources_r17__F2F1.

Opaque TRS_ResourceSet_r17__nrofResources_r17__cond TRS_ResourceSet_r17__nrofResources_r17__Format.


Definition TRS_ResourceSet_r17__Format_Type := Eval cbn in seq_format_prod TRS_ResourceSet_r17__list.
Definition TRS_ResourceSet_r17__Format_list : TRS_ResourceSet_r17__Format_Type :=
  (TRS_ResourceSet_r17__powerControlOffsetSS_r17__Format, (TRS_ResourceSet_r17__scramblingID_Info_r17__Format, (TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17__Format, (TRS_ResourceSet_r17__startingRB_r17__Format, (TRS_ResourceSet_r17__nrofRBs_r17__Format, (SSB_Index__Format, (TRS_ResourceSet_r17__periodicityAndOffset_r17__Format, (TRS_ResourceSet_r17__frequencyDomainAllocation_r17__Format, (TRS_ResourceSet_r17__indBitID_r17__Format, (TRS_ResourceSet_r17__nrofResources_r17__Format, unit_format)))))))))).
Definition TRS_ResourceSet_r17__list__Format := (*Eval compute in *) seq_format TRS_ResourceSet_r17__list TRS_ResourceSet_r17__Format_list.
Definition TRS_ResourceSet_r17__F1 z :=
  (TRS_ResourceSet_r17__powerControlOffsetSS_r17 z, (TRS_ResourceSet_r17__scramblingID_Info_r17 z, (TRS_ResourceSet_r17__firstOFDMSymbolInTimeDomain_r17 z, (TRS_ResourceSet_r17__startingRB_r17 z, (TRS_ResourceSet_r17__nrofRBs_r17 z, (TRS_ResourceSet_r17__ssb_Index_r17 z, (TRS_ResourceSet_r17__periodicityAndOffset_r17 z, (TRS_ResourceSet_r17__frequencyDomainAllocation_r17 z, (TRS_ResourceSet_r17__indBitID_r17 z, (TRS_ResourceSet_r17__nrofResources_r17 z, tt)))))))))).
Definition TRS_ResourceSet_r17__F2 (y : seq_type TRS_ResourceSet_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__TRS_ResourceSet_r17__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma TRS_ResourceSet_r17__F1F2_cond (z : TRS_ResourceSet_r17__Type)
  : TRS_ResourceSet_r17__cond z ->
  (seq_cond TRS_ResourceSet_r17__list (TRS_ResourceSet_r17__F1 z)).
intro H. unfold TRS_ResourceSet_r17__cond in H. simpl. auto. Qed.
Lemma TRS_ResourceSet_r17__F1F2_cond2 (z : TRS_ResourceSet_r17__Type)
 : TRS_ResourceSet_r17__F2 (TRS_ResourceSet_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TRS_ResourceSet_r17__F2F1_cond (y : seq_type TRS_ResourceSet_r17__list)
  : seq_cond TRS_ResourceSet_r17__list y ->
 (TRS_ResourceSet_r17__cond (TRS_ResourceSet_r17__F2 y)) /\  TRS_ResourceSet_r17__F1 (TRS_ResourceSet_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TRS_ResourceSet_r17__cond. simpl in *. auto.
 - simpl. unfold TRS_ResourceSet_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TRS_ResourceSet_r17__Format : T_Format TRS_ResourceSet_r17__Type TRS_ResourceSet_r17__cond :=
        proj2_format  TRS_ResourceSet_r17__cond TRS_ResourceSet_r17__list__Format
    TRS_ResourceSet_r17__F1 TRS_ResourceSet_r17__F2 TRS_ResourceSet_r17__F1F2_cond  TRS_ResourceSet_r17__F1F2_cond2 TRS_ResourceSet_r17__F2F1_cond.
Opaque TRS_ResourceSet_r17__cond TRS_ResourceSet_r17__Format.

