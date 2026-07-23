Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_ResourceSetId.

Opaque SRS_ResourceSetId__cond SRS_ResourceSetId__Format.

Definition SRS_Config__srs_ResourceSetToReleaseList__Type := list SRS_ResourceSetId__Type.

Lemma SRS_Config__srs_ResourceSetToReleaseList__helper1 : (0 <= 1 <= maxNrofSRS_ResourceSets)%Z. unfold maxNrofSRS_ResourceSets.
 lia. Qed.
Lemma SRS_Config__srs_ResourceSetToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__srs_ResourceSetToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__srs_ResourceSetToReleaseList__cond (z : SRS_Config__srs_ResourceSetToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_ResourceSets)%Z /\ (list_and SRS_ResourceSetId__cond z) .

Require Import NR.SRS_ResourceSet.

Opaque SRS_ResourceSet__cond SRS_ResourceSet__Format.

Definition SRS_Config__srs_ResourceSetToAddModList__Type := list SRS_ResourceSet__Type.

Lemma SRS_Config__srs_ResourceSetToAddModList__helper1 : (0 <= 1 <= maxNrofSRS_ResourceSets)%Z. unfold maxNrofSRS_ResourceSets.
 lia. Qed.
Lemma SRS_Config__srs_ResourceSetToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__srs_ResourceSetToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__srs_ResourceSetToAddModList__cond (z : SRS_Config__srs_ResourceSetToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_ResourceSets)%Z /\ (list_and SRS_ResourceSet__cond z) .

Require Import NR.SRS_ResourceId.

Opaque SRS_ResourceId__cond SRS_ResourceId__Format.

Definition SRS_Config__srs_ResourceToReleaseList__Type := list SRS_ResourceId__Type.

Lemma SRS_Config__srs_ResourceToReleaseList__helper1 : (0 <= 1 <= maxNrofSRS_Resources)%Z. unfold maxNrofSRS_Resources.
 lia. Qed.
Lemma SRS_Config__srs_ResourceToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__srs_ResourceToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__srs_ResourceToReleaseList__cond (z : SRS_Config__srs_ResourceToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_Resources)%Z /\ (list_and SRS_ResourceId__cond z) .

Require Import NR.SRS_Resource.

Opaque SRS_Resource__cond SRS_Resource__Format.

Definition SRS_Config__srs_ResourceToAddModList__Type := list SRS_Resource__Type.

Lemma SRS_Config__srs_ResourceToAddModList__helper1 : (0 <= 1 <= maxNrofSRS_Resources)%Z. unfold maxNrofSRS_Resources.
 lia. Qed.
Lemma SRS_Config__srs_ResourceToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__srs_ResourceToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__srs_ResourceToAddModList__cond (z : SRS_Config__srs_ResourceToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_Resources)%Z /\ (list_and SRS_Resource__cond z) .

Inductive SRS_Config__tpc_Accumulation__Type : Set :=
 | SRS_Config__tpc_Accumulation__disabled
.
Definition SRS_Config__tpc_Accumulation__cond := (fun (_ : SRS_Config__tpc_Accumulation__Type) => True).
Lemma SRS_Config__tpc_Accumulation__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Config__tpc_Accumulation__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SRS_Config__tpc_Accumulation__nat__helper.

Definition SRS_Config__tpc_Accumulation__F1 t :=
  match t with
  | SRS_Config__tpc_Accumulation__disabled => 0
  end.
Definition SRS_Config__tpc_Accumulation__F2 n :=
  match n with
  | 0 => SRS_Config__tpc_Accumulation__disabled
  | _ => SRS_Config__tpc_Accumulation__disabled
  end.
Lemma SRS_Config__tpc_Accumulation__F1F2 : forall x : SRS_Config__tpc_Accumulation__Type, (SRS_Config__tpc_Accumulation__F1 x <= 0) /\ SRS_Config__tpc_Accumulation__F2 (SRS_Config__tpc_Accumulation__F1 x) = x. imp_solve. Qed.
Lemma SRS_Config__tpc_Accumulation__F2F1 : forall (y : nat) (H : y <= 0), SRS_Config__tpc_Accumulation__F1 (SRS_Config__tpc_Accumulation__F2 y) = y. enum_solve H y. Qed.

Lemma SRS_Config__ext0O__srs_RequestDCI_1_2_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma SRS_Config__ext0O__srs_RequestDCI_1_2_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__ext0O__srs_RequestDCI_1_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__ext0O__srs_RequestDCI_1_2_r16__Type := Z.
Definition SRS_Config__ext0O__srs_RequestDCI_1_2_r16__cond := (fun z => (1 <= z <= 2)%Z).
Lemma SRS_Config__ext0O__srs_RequestDCI_0_2_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma SRS_Config__ext0O__srs_RequestDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__ext0O__srs_RequestDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__ext0O__srs_RequestDCI_0_2_r16__Type := Z.
Definition SRS_Config__ext0O__srs_RequestDCI_0_2_r16__cond := (fun z => (1 <= z <= 2)%Z).
Require Import NR.SRS_ResourceSet.

Opaque SRS_ResourceSet__cond SRS_ResourceSet__Format.

Definition SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__Type := list SRS_ResourceSet__Type.

Lemma SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__helper1 : (0 <= 1 <= maxNrofSRS_ResourceSets)%Z. unfold maxNrofSRS_ResourceSets.
 lia. Qed.
Lemma SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__cond (z : SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_ResourceSets)%Z /\ (list_and SRS_ResourceSet__cond z) .

Require Import NR.SRS_ResourceSetId.

Opaque SRS_ResourceSetId__cond SRS_ResourceSetId__Format.

Definition SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__Type := list SRS_ResourceSetId__Type.

Lemma SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__helper1 : (0 <= 1 <= maxNrofSRS_ResourceSets)%Z. unfold maxNrofSRS_ResourceSets.
 lia. Qed.
Lemma SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__cond (z : SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_ResourceSets)%Z /\ (list_and SRS_ResourceSetId__cond z) .

Require Import NR.SRS_PosResourceSetId_r16.

Opaque SRS_PosResourceSetId_r16__cond SRS_PosResourceSetId_r16__Format.

Definition SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__Type := list SRS_PosResourceSetId_r16__Type.

Lemma SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofSRS_PosResourceSets_r16)%Z. unfold maxNrofSRS_PosResourceSets_r16.
 lia. Qed.
Lemma SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_PosResourceSets_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_PosResourceSets_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__cond (z : SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_PosResourceSets_r16)%Z /\ (list_and SRS_PosResourceSetId_r16__cond z) .

Require Import NR.SRS_PosResourceSet_r16.

Opaque SRS_PosResourceSet_r16__cond SRS_PosResourceSet_r16__Format.

Definition SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__Type := list SRS_PosResourceSet_r16__Type.

Lemma SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__helper1 : (0 <= 1 <= maxNrofSRS_PosResourceSets_r16)%Z. unfold maxNrofSRS_PosResourceSets_r16.
 lia. Qed.
Lemma SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_PosResourceSets_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_PosResourceSets_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__cond (z : SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_PosResourceSets_r16)%Z /\ (list_and SRS_PosResourceSet_r16__cond z) .

Require Import NR.SRS_PosResourceId_r16.

Opaque SRS_PosResourceId_r16__cond SRS_PosResourceId_r16__Format.

Definition SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__Type := list SRS_PosResourceId_r16__Type.

Lemma SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofSRS_PosResources_r16)%Z. unfold maxNrofSRS_PosResources_r16.
 lia. Qed.
Lemma SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_PosResources_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_PosResources_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__cond (z : SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_PosResources_r16)%Z /\ (list_and SRS_PosResourceId_r16__cond z) .

Require Import NR.SRS_PosResource_r16.

Opaque SRS_PosResource_r16__cond SRS_PosResource_r16__Format.

Definition SRS_Config__ext0O__srs_PosResourceToAddModList_r16__Type := list SRS_PosResource_r16__Type.

Lemma SRS_Config__ext0O__srs_PosResourceToAddModList_r16__helper1 : (0 <= 1 <= maxNrofSRS_PosResources_r16)%Z. unfold maxNrofSRS_PosResources_r16.
 lia. Qed.
Lemma SRS_Config__ext0O__srs_PosResourceToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_PosResources_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_PosResources_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Config__ext0O__srs_PosResourceToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Config__ext0O__srs_PosResourceToAddModList_r16__cond (z : SRS_Config__ext0O__srs_PosResourceToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_PosResources_r16)%Z /\ (list_and SRS_PosResource_r16__cond z) .

Record SRS_Config__ext0O__Type : Set :=
  make__SRS_Config__ext0O__Type {
    SRS_Config__ext0O__srs_RequestDCI_1_2_r16 : option Z ;
    SRS_Config__ext0O__srs_RequestDCI_0_2_r16 : option Z ;
    SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16 : option SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__Type ;
    SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16 : option SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__Type ;
    SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16 : option SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__Type ;
    SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16 : option SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__Type ;
    SRS_Config__ext0O__srs_PosResourceToReleaseList_r16 : option SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__Type ;
    SRS_Config__ext0O__srs_PosResourceToAddModList_r16 : option SRS_Config__ext0O__srs_PosResourceToAddModList_r16__Type ;
}.
Definition SRS_Config__ext0O__list := (
 Opt Z SRS_Config__ext0O__srs_RequestDCI_1_2_r16__cond ::
 Opt Z SRS_Config__ext0O__srs_RequestDCI_0_2_r16__cond ::
 Opt SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__Type SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__cond ::
 Opt SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__Type SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__cond ::
 Opt SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__Type SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__cond ::
 Opt SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__Type SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__cond ::
 Opt SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__Type SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__cond ::
 Opt SRS_Config__ext0O__srs_PosResourceToAddModList_r16__Type SRS_Config__ext0O__srs_PosResourceToAddModList_r16__cond ::
 nil).
Definition SRS_Config__ext0O__cond z := 
  opt_cond SRS_Config__ext0O__srs_RequestDCI_1_2_r16__cond (SRS_Config__ext0O__srs_RequestDCI_1_2_r16 z) /\
  opt_cond SRS_Config__ext0O__srs_RequestDCI_0_2_r16__cond (SRS_Config__ext0O__srs_RequestDCI_0_2_r16 z) /\
  opt_cond SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__cond (SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16 z) /\
  opt_cond SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__cond (SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16 z) /\
  opt_cond SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__cond (SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16 z) /\
  opt_cond SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__cond (SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16 z) /\
  opt_cond SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__cond (SRS_Config__ext0O__srs_PosResourceToReleaseList_r16 z) /\
  opt_cond SRS_Config__ext0O__srs_PosResourceToAddModList_r16__cond (SRS_Config__ext0O__srs_PosResourceToAddModList_r16 z) /\
  True.

Definition SRS_Config__ext0__Type := SRS_Config__ext0O__Type.
Definition SRS_Config__ext0__cond := SRS_Config__ext0O__cond.

Record SRS_Config__Type : Set :=
  make__SRS_Config__Type {
    SRS_Config__srs_ResourceSetToReleaseList : option SRS_Config__srs_ResourceSetToReleaseList__Type ;
    SRS_Config__srs_ResourceSetToAddModList : option SRS_Config__srs_ResourceSetToAddModList__Type ;
    SRS_Config__srs_ResourceToReleaseList : option SRS_Config__srs_ResourceToReleaseList__Type ;
    SRS_Config__srs_ResourceToAddModList : option SRS_Config__srs_ResourceToAddModList__Type ;
    SRS_Config__tpc_Accumulation : option SRS_Config__tpc_Accumulation__Type ;
    SRS_Config__ext0 : option SRS_Config__ext0__Type ;
}.
Definition SRS_Config__root_list : list seq_elem := (
 Opt SRS_Config__srs_ResourceSetToReleaseList__Type SRS_Config__srs_ResourceSetToReleaseList__cond ::
 Opt SRS_Config__srs_ResourceSetToAddModList__Type SRS_Config__srs_ResourceSetToAddModList__cond ::
 Opt SRS_Config__srs_ResourceToReleaseList__Type SRS_Config__srs_ResourceToReleaseList__cond ::
 Opt SRS_Config__srs_ResourceToAddModList__Type SRS_Config__srs_ResourceToAddModList__cond ::
 Opt SRS_Config__tpc_Accumulation__Type SRS_Config__tpc_Accumulation__cond ::
 nil).
Definition SRS_Config__ext_list : list typ := (
  typ_cons SRS_Config__ext0__Type SRS_Config__ext0__cond ::
  nil).
Definition SRS_Config__cond (z : SRS_Config__Type) := 
(  opt_cond SRS_Config__srs_ResourceSetToReleaseList__cond (SRS_Config__srs_ResourceSetToReleaseList z) /\
  opt_cond SRS_Config__srs_ResourceSetToAddModList__cond (SRS_Config__srs_ResourceSetToAddModList z) /\
  opt_cond SRS_Config__srs_ResourceToReleaseList__cond (SRS_Config__srs_ResourceToReleaseList z) /\
  opt_cond SRS_Config__srs_ResourceToAddModList__cond (SRS_Config__srs_ResourceToAddModList z) /\
  opt_cond SRS_Config__tpc_Accumulation__cond (SRS_Config__tpc_Accumulation z) /\
  True) /\ 
(  opt_cond SRS_Config__ext0__cond (SRS_Config__ext0 z) /\
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
Definition SRS_Config__srs_ResourceSetToReleaseList__Format : T_Format SRS_Config__srs_ResourceSetToReleaseList__Type SRS_Config__srs_ResourceSetToReleaseList__cond := seq_of_format SRS_ResourceSetId__Format 1 maxNrofSRS_ResourceSets SRS_Config__srs_ResourceSetToReleaseList__helper1 SRS_Config__srs_ResourceSetToReleaseList__helper2.

Opaque SRS_Config__srs_ResourceSetToReleaseList__cond SRS_Config__srs_ResourceSetToReleaseList__Format.

Definition SRS_Config__srs_ResourceSetToAddModList__Format : T_Format SRS_Config__srs_ResourceSetToAddModList__Type SRS_Config__srs_ResourceSetToAddModList__cond := seq_of_format SRS_ResourceSet__Format 1 maxNrofSRS_ResourceSets SRS_Config__srs_ResourceSetToAddModList__helper1 SRS_Config__srs_ResourceSetToAddModList__helper2.

Opaque SRS_Config__srs_ResourceSetToAddModList__cond SRS_Config__srs_ResourceSetToAddModList__Format.

Definition SRS_Config__srs_ResourceToReleaseList__Format : T_Format SRS_Config__srs_ResourceToReleaseList__Type SRS_Config__srs_ResourceToReleaseList__cond := seq_of_format SRS_ResourceId__Format 1 maxNrofSRS_Resources SRS_Config__srs_ResourceToReleaseList__helper1 SRS_Config__srs_ResourceToReleaseList__helper2.

Opaque SRS_Config__srs_ResourceToReleaseList__cond SRS_Config__srs_ResourceToReleaseList__Format.

Definition SRS_Config__srs_ResourceToAddModList__Format : T_Format SRS_Config__srs_ResourceToAddModList__Type SRS_Config__srs_ResourceToAddModList__cond := seq_of_format SRS_Resource__Format 1 maxNrofSRS_Resources SRS_Config__srs_ResourceToAddModList__helper1 SRS_Config__srs_ResourceToAddModList__helper2.

Opaque SRS_Config__srs_ResourceToAddModList__cond SRS_Config__srs_ResourceToAddModList__Format.

Definition SRS_Config__tpc_Accumulation__Format : T_Format SRS_Config__tpc_Accumulation__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Config__tpc_Accumulation__nat__Format SRS_Config__tpc_Accumulation__F1 SRS_Config__tpc_Accumulation__F2 SRS_Config__tpc_Accumulation__F1F2 SRS_Config__tpc_Accumulation__F2F1.

Opaque SRS_Config__tpc_Accumulation__cond SRS_Config__tpc_Accumulation__Format.

Definition SRS_Config__ext0O__srs_RequestDCI_1_2_r16__Format : T_Format Z SRS_Config__ext0O__srs_RequestDCI_1_2_r16__cond :=
 ranged_int_format (1) (2) SRS_Config__ext0O__srs_RequestDCI_1_2_r16__helper1 SRS_Config__ext0O__srs_RequestDCI_1_2_r16__helper2.

Opaque SRS_Config__ext0O__srs_RequestDCI_1_2_r16__cond SRS_Config__ext0O__srs_RequestDCI_1_2_r16__Format.

Definition SRS_Config__ext0O__srs_RequestDCI_0_2_r16__Format : T_Format Z SRS_Config__ext0O__srs_RequestDCI_0_2_r16__cond :=
 ranged_int_format (1) (2) SRS_Config__ext0O__srs_RequestDCI_0_2_r16__helper1 SRS_Config__ext0O__srs_RequestDCI_0_2_r16__helper2.

Opaque SRS_Config__ext0O__srs_RequestDCI_0_2_r16__cond SRS_Config__ext0O__srs_RequestDCI_0_2_r16__Format.

Definition SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__Format : T_Format SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__Type SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__cond := seq_of_format SRS_ResourceSet__Format 1 maxNrofSRS_ResourceSets SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__helper1 SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__helper2.

Opaque SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__cond SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__Format.

Definition SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__Format : T_Format SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__Type SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__cond := seq_of_format SRS_ResourceSetId__Format 1 maxNrofSRS_ResourceSets SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__helper1 SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__helper2.

Opaque SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__cond SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__Format.

Definition SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__Format : T_Format SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__Type SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__cond := seq_of_format SRS_PosResourceSetId_r16__Format 1 maxNrofSRS_PosResourceSets_r16 SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__helper1 SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__helper2.

Opaque SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__cond SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__Format.

Definition SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__Format : T_Format SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__Type SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__cond := seq_of_format SRS_PosResourceSet_r16__Format 1 maxNrofSRS_PosResourceSets_r16 SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__helper1 SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__helper2.

Opaque SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__cond SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__Format.

Definition SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__Format : T_Format SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__Type SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__cond := seq_of_format SRS_PosResourceId_r16__Format 1 maxNrofSRS_PosResources_r16 SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__helper1 SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__helper2.

Opaque SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__cond SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__Format.

Definition SRS_Config__ext0O__srs_PosResourceToAddModList_r16__Format : T_Format SRS_Config__ext0O__srs_PosResourceToAddModList_r16__Type SRS_Config__ext0O__srs_PosResourceToAddModList_r16__cond := seq_of_format SRS_PosResource_r16__Format 1 maxNrofSRS_PosResources_r16 SRS_Config__ext0O__srs_PosResourceToAddModList_r16__helper1 SRS_Config__ext0O__srs_PosResourceToAddModList_r16__helper2.

Opaque SRS_Config__ext0O__srs_PosResourceToAddModList_r16__cond SRS_Config__ext0O__srs_PosResourceToAddModList_r16__Format.


Definition SRS_Config__ext0O__Format_Type := Eval cbn in seq_format_prod SRS_Config__ext0O__list.
Definition SRS_Config__ext0O__Format_list : SRS_Config__ext0O__Format_Type :=
  (SRS_Config__ext0O__srs_RequestDCI_1_2_r16__Format, (SRS_Config__ext0O__srs_RequestDCI_0_2_r16__Format, (SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16__Format, (SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16__Format, (SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16__Format, (SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16__Format, (SRS_Config__ext0O__srs_PosResourceToReleaseList_r16__Format, (SRS_Config__ext0O__srs_PosResourceToAddModList_r16__Format, unit_format)))))))).
Definition SRS_Config__ext0O__list__Format := (*Eval compute in *) seq_format SRS_Config__ext0O__list SRS_Config__ext0O__Format_list.
Definition SRS_Config__ext0O__F1 z :=
  (SRS_Config__ext0O__srs_RequestDCI_1_2_r16 z, (SRS_Config__ext0O__srs_RequestDCI_0_2_r16 z, (SRS_Config__ext0O__srs_ResourceSetToAddModListDCI_0_2_r16 z, (SRS_Config__ext0O__srs_ResourceSetToReleaseListDCI_0_2_r16 z, (SRS_Config__ext0O__srs_PosResourceSetToReleaseList_r16 z, (SRS_Config__ext0O__srs_PosResourceSetToAddModList_r16 z, (SRS_Config__ext0O__srs_PosResourceToReleaseList_r16 z, (SRS_Config__ext0O__srs_PosResourceToAddModList_r16 z, tt)))))))).
Definition SRS_Config__ext0O__F2 (y : seq_type SRS_Config__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__SRS_Config__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma SRS_Config__ext0O__F1F2_cond (z : SRS_Config__ext0O__Type)
  : SRS_Config__ext0O__cond z ->
  (seq_cond SRS_Config__ext0O__list (SRS_Config__ext0O__F1 z)).
intro H. unfold SRS_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma SRS_Config__ext0O__F1F2_cond2 (z : SRS_Config__ext0O__Type)
 : SRS_Config__ext0O__F2 (SRS_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Config__ext0O__F2F1_cond (y : seq_type SRS_Config__ext0O__list)
  : seq_cond SRS_Config__ext0O__list y ->
 (SRS_Config__ext0O__cond (SRS_Config__ext0O__F2 y)) /\  SRS_Config__ext0O__F1 (SRS_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold SRS_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Config__ext0O__Format : T_Format SRS_Config__ext0O__Type SRS_Config__ext0O__cond :=
        proj2_format  SRS_Config__ext0O__cond SRS_Config__ext0O__list__Format
    SRS_Config__ext0O__F1 SRS_Config__ext0O__F2 SRS_Config__ext0O__F1F2_cond  SRS_Config__ext0O__F1F2_cond2 SRS_Config__ext0O__F2F1_cond.
Opaque SRS_Config__ext0O__cond SRS_Config__ext0O__Format.

Definition SRS_Config__ext0__check_all_none (b : SRS_Config__ext0O__Type) : bool :=
match b with 
  | make__SRS_Config__ext0O__Type None None None None None None None None  => false 
  | _ => true 
 end.
Definition SRS_Config__ext0__Format : T_Format SRS_Config__ext0__Type SRS_Config__ext0__cond :=
  restrict_add_format SRS_Config__ext0__check_all_none SRS_Config__ext0O__Format.

Opaque SRS_Config__ext0__cond SRS_Config__ext0__Format.


Definition SRS_Config__root_Format_Type := Eval cbn in seq_format_prod SRS_Config__root_list.
Definition SRS_Config__root_Format_list : SRS_Config__root_Format_Type :=
  (SRS_Config__srs_ResourceSetToReleaseList__Format, (SRS_Config__srs_ResourceSetToAddModList__Format, (SRS_Config__srs_ResourceToReleaseList__Format, (SRS_Config__srs_ResourceToAddModList__Format, (SRS_Config__tpc_Accumulation__Format, unit_format))))).

Definition SRS_Config__ext_Format_Type := Eval cbn in get_formats SRS_Config__ext_list.
Definition SRS_Config__ext_Format_list : SRS_Config__ext_Format_Type :=
  (SRS_Config__ext0__Format, unit__Format).

Definition SRS_Config__list_type : Set := (seq_type SRS_Config__root_list) * (seq_ext_type SRS_Config__ext_list).
Definition SRS_Config__list_cond (z : SRS_Config__list_type) : Prop :=
        (seq_cond SRS_Config__root_list (fst z)) /\ (seq_ext_cond SRS_Config__ext_list (snd z)).
Definition SRS_Config__list_format : T_Format SRS_Config__list_type SRS_Config__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_Config__root_list SRS_Config__root_Format_list SRS_Config__ext_list SRS_Config__ext_Format_list.

Opaque SRS_Config__list_format.
Definition SRS_Config__F1 (z : SRS_Config__Type) : SRS_Config__list_type :=
  (((SRS_Config__srs_ResourceSetToReleaseList z, (SRS_Config__srs_ResourceSetToAddModList z, (SRS_Config__srs_ResourceToReleaseList z, (SRS_Config__srs_ResourceToAddModList z, (SRS_Config__tpc_Accumulation z, tt)))))), (
(SRS_Config__ext0 z, tt))).
Definition SRS_Config__F2 (y : SRS_Config__list_type) : SRS_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, _))=>
    make__SRS_Config__Type j0 j1 j2 j3 j4 i0
  end.
Definition SRS_Config__helper1 : (forall a : SRS_Config__Type, SRS_Config__cond a -> SRS_Config__list_cond (SRS_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_Config__helper2 : (forall a : SRS_Config__Type, SRS_Config__F2 (SRS_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_Config__helper3 : (forall b : SRS_Config__list_type, SRS_Config__list_cond b -> SRS_Config__cond (SRS_Config__F2 b) /\ SRS_Config__F1 (SRS_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_Config__cond, SRS_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_Config__Format : T_Format SRS_Config__Type SRS_Config__cond :=
 proj2_format SRS_Config__cond SRS_Config__list_format  SRS_Config__F1 SRS_Config__F2 SRS_Config__helper1 SRS_Config__helper2 SRS_Config__helper3.

Opaque SRS_Config__cond SRS_Config__Format.

