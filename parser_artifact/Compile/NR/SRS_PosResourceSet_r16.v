Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_PosResourceSetId_r16.

Opaque SRS_PosResourceSetId_r16__cond SRS_PosResourceSetId_r16__Format.

Require Import NR.SRS_PosResourceId_r16.

Opaque SRS_PosResourceId_r16__cond SRS_PosResourceId_r16__Format.

Definition SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__Type := list SRS_PosResourceId_r16__Type.

Lemma SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__helper1 : (0 <= 1 <= maxNrofSRS_ResourcesPerSet)%Z. unfold maxNrofSRS_ResourcesPerSet.
 lia. Qed.
Lemma SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_ResourcesPerSet - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_ResourcesPerSet - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__cond (z : SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_ResourcesPerSet)%Z /\ (list_and SRS_PosResourceId_r16__cond z) .

Lemma SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__helper1 : (1 <= maxNrofSRS_TriggerStates_1)%Z. unfold maxNrofSRS_TriggerStates_1.
 lia. Qed.
Lemma SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_TriggerStates_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_TriggerStates_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__Type := Z.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__cond := (fun z => (1 <= z <= maxNrofSRS_TriggerStates_1)%Z).
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__Type := list Z.

Lemma SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__helper1 : (0 <= 1 <= maxNrofSRS_TriggerStates_1)%Z. unfold maxNrofSRS_TriggerStates_1.
 lia. Qed.
Lemma SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_TriggerStates_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_TriggerStates_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__cond (z : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_TriggerStates_1)%Z /\ (list_and SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__cond z) .

Record SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type : Set :=
  make__SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type {
    SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16 : option SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__Type ;
}.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_list : list seq_elem := (
 Opt SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__Type SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__cond ::
 nil).
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_list : list typ := (
  nil).
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond (z : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type) := 
(  opt_cond SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__cond (SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16 z) /\
  True) /\ 
(  True).

Record SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Type : Set := make__SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Type {}.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__cond (z : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Type) := True.
Record SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type : Set :=
  make__SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type {
}.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_list : list seq_elem := (
 nil).
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_list : list typ := (
  nil).
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond (z : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type) := 
(  True) /\ 
(  True).

Record SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Type : Set := make__SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Type {}.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__cond (z : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Type) := True.
Record SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type : Set :=
  make__SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type {
}.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_list : list seq_elem := (
 nil).
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_list : list typ := (
  nil).
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond (z : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type) := 
(  True) /\ 
(  True).


Inductive SRS_PosResourceSet_r16__resourceType_r16__Type : Set :=
  | SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16 : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type -> SRS_PosResourceSet_r16__resourceType_r16__Type
  | SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16 : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type -> SRS_PosResourceSet_r16__resourceType_r16__Type
  | SRS_PosResourceSet_r16__resourceType_r16__periodic_r16 : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type -> SRS_PosResourceSet_r16__resourceType_r16__Type
.
Definition SRS_PosResourceSet_r16__resourceType_r16__list : list typ := (
typ_cons SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond ::
typ_cons SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond ::
typ_cons SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond ::
 nil).
Definition SRS_PosResourceSet_r16__resourceType_r16__cond (c : SRS_PosResourceSet_r16__resourceType_r16__Type) := 
  match c with
  | SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16 t => SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond t 
  | SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16 t => SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond t 
  | SRS_PosResourceSet_r16__resourceType_r16__periodic_r16 t => SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond t 
  end.

Lemma SRS_PosResourceSet_r16__resourceType_r16__len_helper1 : to_bit_sz (length SRS_PosResourceSet_r16__resourceType_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_PosResourceSet_r16__resourceType_r16__len_helper2 : 2 <= length2 SRS_PosResourceSet_r16__resourceType_r16__list.
 simpl. lia. Qed.
Require Import NR.Alpha.

Opaque Alpha__cond Alpha__Format.

Lemma SRS_PosResourceSet_r16__p0_r16__helper1 : (-202 <= 24)%Z.  lia. Qed.
Lemma SRS_PosResourceSet_r16__p0_r16__helper2 : to_bit_sz (Z.to_nat (24 - -202)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (24 - -202))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResourceSet_r16__p0_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResourceSet_r16__p0_r16__Type := Z.
Definition SRS_PosResourceSet_r16__p0_r16__cond := (fun z => (-202 <= z <= 24)%Z).
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.SSB_InfoNcell_r16.

Opaque SSB_InfoNcell_r16__cond SSB_InfoNcell_r16__Format.

Require Import NR.DL_PRS_Info_r16.

Opaque DL_PRS_Info_r16__cond DL_PRS_Info_r16__Format.


Inductive SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type : Set :=
  | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__ssb_IndexServing_r16 : SSB_Index__Type -> SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type
  | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__ssb_Ncell_r16 : SSB_InfoNcell_r16__Type -> SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type
  | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__dl_PRS_r16 : DL_PRS_Info_r16__Type -> SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type
.
Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons SSB_InfoNcell_r16__Type SSB_InfoNcell_r16__cond ::
typ_cons DL_PRS_Info_r16__Type DL_PRS_Info_r16__cond ::
 nil).
Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__cond (c : SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type) := 
  match c with
  | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__ssb_IndexServing_r16 t => SSB_Index__cond t 
  | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__ssb_Ncell_r16 t => SSB_InfoNcell_r16__cond t 
  | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__dl_PRS_r16 t => DL_PRS_Info_r16__cond t 
  end.

Lemma SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__len_helper1 : to_bit_sz (length SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__len_helper2 : 2 <= length2 SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list.
 simpl. lia. Qed.
Record SRS_PosResourceSet_r16__Type : Set :=
  make__SRS_PosResourceSet_r16__Type {
    SRS_PosResourceSet_r16__srs_PosResourceSetId_r16 : SRS_PosResourceSetId_r16__Type ;
    SRS_PosResourceSet_r16__srs_PosResourceIdList_r16 : option SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__Type ;
    SRS_PosResourceSet_r16__resourceType_r16 : SRS_PosResourceSet_r16__resourceType_r16__Type ;
    SRS_PosResourceSet_r16__alpha_r16 : option Alpha__Type ;
    SRS_PosResourceSet_r16__p0_r16 : option Z ;
    SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16 : option SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type ;
}.
Definition SRS_PosResourceSet_r16__root_list : list seq_elem := (
 Nor SRS_PosResourceSetId_r16__Type SRS_PosResourceSetId_r16__cond ::
 Opt SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__Type SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__cond ::
 Nor SRS_PosResourceSet_r16__resourceType_r16__Type SRS_PosResourceSet_r16__resourceType_r16__cond ::
 Opt Alpha__Type Alpha__cond ::
 Opt Z SRS_PosResourceSet_r16__p0_r16__cond ::
 Opt SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__cond ::
 nil).
Definition SRS_PosResourceSet_r16__ext_list : list typ := (
  nil).
Definition SRS_PosResourceSet_r16__cond (z : SRS_PosResourceSet_r16__Type) := 
(  SRS_PosResourceSetId_r16__cond (SRS_PosResourceSet_r16__srs_PosResourceSetId_r16 z) /\
  opt_cond SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__cond (SRS_PosResourceSet_r16__srs_PosResourceIdList_r16 z) /\
  SRS_PosResourceSet_r16__resourceType_r16__cond (SRS_PosResourceSet_r16__resourceType_r16 z) /\
  opt_cond Alpha__cond (SRS_PosResourceSet_r16__alpha_r16 z) /\
  opt_cond SRS_PosResourceSet_r16__p0_r16__cond (SRS_PosResourceSet_r16__p0_r16 z) /\
  opt_cond SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__cond (SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16 z) /\
  True) /\ 
(  True).


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
Definition SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__Format : T_Format SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__Type SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__cond := seq_of_format SRS_PosResourceId_r16__Format 1 maxNrofSRS_ResourcesPerSet SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__helper1 SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__helper2.

Opaque SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__cond SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__Format.

Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__Format : T_Format Z SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__cond :=
 ranged_int_format (1) (maxNrofSRS_TriggerStates_1) SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__helper1 SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__helper2.

Opaque SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__cond SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__Format.

Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__Format : T_Format SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__Type SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__cond := seq_of_format SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__seq_of__Format 1 maxNrofSRS_TriggerStates_1 SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__helper1 SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__helper2.

Opaque SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__cond SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__Format.


Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_list.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_Format_list : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_Format_Type :=
  (SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16__Format, unit_format).

Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_list.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_Format_list : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_Format_Type :=
  unit__Format.

Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_type : Set := (seq_type SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_list) * (seq_ext_type SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_list).
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_cond (z : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_type) : Prop :=
        (seq_cond SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_list (snd z)).
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_format : T_Format SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_type SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_list SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__root_Format_list SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_list SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__ext_Format_list.

Opaque SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_format.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F1 (z : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type) : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_type :=
  (((SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__aperiodicSRS_ResourceTriggerList_r16 z, tt)), (
tt)).
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F2 (y : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_type) : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type j0
  end.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__helper1 : (forall a : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type, SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond a -> SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_cond (SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__helper2 : (forall a : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type, SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F2 (SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__helper3 : (forall b : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_type, SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_cond b -> SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond (SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F2 b) /\ SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F1 (SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond, SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Format : T_Format SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond :=
 proj2_format SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__list_format  SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F1 SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__F2 SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__helper1 SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__helper2 SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__helper3.

Opaque SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__cond SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Format.

Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__helper : forall a : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Type, True -> True /\ make__SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Format : T_Format SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Type SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Type)
    SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__helper unit_unique (fun _ => left I).

Opaque SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__cond SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root__Format.


Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_list.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_Format_list : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_Format_Type :=
  unit_format.

Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_list.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_Format_list : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_Format_Type :=
  unit__Format.

Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_type : Set := (seq_type SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_list) * (seq_ext_type SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_list).
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_cond (z : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_type) : Prop :=
        (seq_cond SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_list (snd z)).
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_format : T_Format SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_type SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_list SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__root_Format_list SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_list SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__ext_Format_list.

Opaque SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_format.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F1 (z : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type) : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_type :=
  ((tt), (
tt)).
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F2 (y : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_type) : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type :=
  match y with
  | (_, _)=>
    make__SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type
  end.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__helper1 : (forall a : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type, SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond a -> SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_cond (SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__helper2 : (forall a : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type, SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F2 (SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__helper3 : (forall b : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_type, SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_cond b -> SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond (SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F2 b) /\ SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F1 (SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond, SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Format : T_Format SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond :=
 proj2_format SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__list_format  SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F1 SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__F2 SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__helper1 SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__helper2 SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__helper3.

Opaque SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__cond SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Format.

Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__helper : forall a : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Type, True -> True /\ make__SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Format : T_Format SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Type SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Type)
    SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__helper unit_unique (fun _ => left I).

Opaque SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__cond SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root__Format.


Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_list.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_Format_list : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_Format_Type :=
  unit_format.

Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_list.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_Format_list : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_Format_Type :=
  unit__Format.

Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_type : Set := (seq_type SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_list) * (seq_ext_type SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_list).
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_cond (z : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_type) : Prop :=
        (seq_cond SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_list (snd z)).
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_format : T_Format SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_type SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_list SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__root_Format_list SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_list SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__ext_Format_list.

Opaque SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_format.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F1 (z : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type) : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_type :=
  ((tt), (
tt)).
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F2 (y : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_type) : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type :=
  match y with
  | (_, _)=>
    make__SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type
  end.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__helper1 : (forall a : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type, SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond a -> SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_cond (SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__helper2 : (forall a : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type, SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F2 (SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__helper3 : (forall b : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_type, SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_cond b -> SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond (SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F2 b) /\ SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F1 (SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond, SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Format : T_Format SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond :=
 proj2_format SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__list_format  SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F1 SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__F2 SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__helper1 SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__helper2 SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__helper3.

Opaque SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__cond SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Format.


Definition SRS_PosResourceSet_r16__resourceType_r16__Format_Type := Eval cbn in get_formats SRS_PosResourceSet_r16__resourceType_r16__list.
Definition SRS_PosResourceSet_r16__resourceType_r16__Format_list : SRS_PosResourceSet_r16__resourceType_r16__Format_Type :=
  (SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Format, (SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Format, (SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Format, unit__Format))).
Definition SRS_PosResourceSet_r16__resourceType_r16__list__Format := Eval compute in choice_format SRS_PosResourceSet_r16__resourceType_r16__list SRS_PosResourceSet_r16__resourceType_r16__len_helper1 SRS_PosResourceSet_r16__resourceType_r16__len_helper2  SRS_PosResourceSet_r16__resourceType_r16__Format_list.
Definition SRS_PosResourceSet_r16__resourceType_r16__F1 (z : SRS_PosResourceSet_r16__resourceType_r16__Type) : (choice SRS_PosResourceSet_r16__resourceType_r16__list) :=
  match z with
   | SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16 t => existT _ 0 t
  | SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16 t => existT _ 1 t
  | SRS_PosResourceSet_r16__resourceType_r16__periodic_r16 t => existT _ 2 t
  end.
Definition SRS_PosResourceSet_r16__resourceType_r16__g := (fun n => typ_set (get_nth_typ SRS_PosResourceSet_r16__resourceType_r16__list n)).
Definition SRS_PosResourceSet_r16__resourceType_r16__F2 (y : choice SRS_PosResourceSet_r16__resourceType_r16__list) : SRS_PosResourceSet_r16__resourceType_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_PosResourceSet_r16__resourceType_r16__g n -> SRS_PosResourceSet_r16__resourceType_r16__Type) with
    | 0 => fun (t : SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16__Type) => SRS_PosResourceSet_r16__resourceType_r16__aperiodic_r16 t 
    | 1 => fun (t : SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16__Type) => SRS_PosResourceSet_r16__resourceType_r16__semi_persistent_r16 t 
    | 2 => fun (t : SRS_PosResourceSet_r16__resourceType_r16__periodic_r16__Type) => SRS_PosResourceSet_r16__resourceType_r16__periodic_r16 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SRS_PosResourceSet_r16__resourceType_r16__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SRS_PosResourceSet_r16__resourceType_r16__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_PosResourceSet_r16__resourceType_r16__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SRS_PosResourceSet_r16__resourceType_r16__Type with end) n0
           end t0).

Lemma SRS_PosResourceSet_r16__resourceType_r16__helper2 :  forall (y : SRS_PosResourceSet_r16__resourceType_r16__Type), SRS_PosResourceSet_r16__resourceType_r16__cond y -> choice_cond SRS_PosResourceSet_r16__resourceType_r16__list (SRS_PosResourceSet_r16__resourceType_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_PosResourceSet_r16__resourceType_r16__helper3 :  forall (y : SRS_PosResourceSet_r16__resourceType_r16__Type), SRS_PosResourceSet_r16__resourceType_r16__F2 (SRS_PosResourceSet_r16__resourceType_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_PosResourceSet_r16__resourceType_r16__helper4 : (forall b : choice SRS_PosResourceSet_r16__resourceType_r16__list, choice_cond SRS_PosResourceSet_r16__resourceType_r16__list b -> SRS_PosResourceSet_r16__resourceType_r16__cond (SRS_PosResourceSet_r16__resourceType_r16__F2 b) /\ SRS_PosResourceSet_r16__resourceType_r16__F1 (SRS_PosResourceSet_r16__resourceType_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_PosResourceSet_r16__resourceType_r16__F1 SRS_PosResourceSet_r16__resourceType_r16__F2.
Definition SRS_PosResourceSet_r16__resourceType_r16__Format : T_Format SRS_PosResourceSet_r16__resourceType_r16__Type SRS_PosResourceSet_r16__resourceType_r16__cond :=
  (* Eval compute in *) proj2_format SRS_PosResourceSet_r16__resourceType_r16__cond SRS_PosResourceSet_r16__resourceType_r16__list__Format SRS_PosResourceSet_r16__resourceType_r16__F1 SRS_PosResourceSet_r16__resourceType_r16__F2 SRS_PosResourceSet_r16__resourceType_r16__helper2 SRS_PosResourceSet_r16__resourceType_r16__helper3 SRS_PosResourceSet_r16__resourceType_r16__helper4.
Opaque SRS_PosResourceSet_r16__resourceType_r16__cond SRS_PosResourceSet_r16__resourceType_r16__Format.

Definition SRS_PosResourceSet_r16__p0_r16__Format : T_Format Z SRS_PosResourceSet_r16__p0_r16__cond :=
 ranged_int_format (-202) (24) SRS_PosResourceSet_r16__p0_r16__helper1 SRS_PosResourceSet_r16__p0_r16__helper2.

Opaque SRS_PosResourceSet_r16__p0_r16__cond SRS_PosResourceSet_r16__p0_r16__Format.


Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Format_Type := Eval cbn in get_formats SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list.
Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Format_list : SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Format_Type :=
  (SSB_Index__Format, (SSB_InfoNcell_r16__Format, (DL_PRS_Info_r16__Format, unit__Format))).
Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list__Format := Eval compute in choice_format SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__len_helper1 SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__len_helper2  SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Format_list.
Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F1 (z : SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type) : (choice SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list) :=
  match z with
   | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__ssb_IndexServing_r16 t => existT _ 0 t
  | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__ssb_Ncell_r16 t => existT _ 1 t
  | SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__dl_PRS_r16 t => existT _ 2 t
  end.
Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__g := (fun n => typ_set (get_nth_typ SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list n)).
Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F2 (y : choice SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list) : SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__g n -> SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type) with
    | 0 => fun (t : SSB_Index__Type) => SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__ssb_IndexServing_r16 t 
    | 1 => fun (t : SSB_InfoNcell_r16__Type) => SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__ssb_Ncell_r16 t 
    | 2 => fun (t : DL_PRS_Info_r16__Type) => SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__dl_PRS_r16 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type with end) n0
           end t0).

Lemma SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__helper2 :  forall (y : SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type), SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__cond y -> choice_cond SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list (SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__helper3 :  forall (y : SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type), SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F2 (SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__helper4 : (forall b : choice SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list, choice_cond SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list b -> SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__cond (SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F2 b) /\ SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F1 (SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F1 SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F2.
Definition SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Format : T_Format SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Type SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__cond :=
  (* Eval compute in *) proj2_format SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__cond SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__list__Format SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F1 SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__F2 SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__helper2 SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__helper3 SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__helper4.
Opaque SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__cond SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Format.


Definition SRS_PosResourceSet_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResourceSet_r16__root_list.
Definition SRS_PosResourceSet_r16__root_Format_list : SRS_PosResourceSet_r16__root_Format_Type :=
  (SRS_PosResourceSetId_r16__Format, (SRS_PosResourceSet_r16__srs_PosResourceIdList_r16__Format, (SRS_PosResourceSet_r16__resourceType_r16__Format, (Alpha__Format, (SRS_PosResourceSet_r16__p0_r16__Format, (SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16__Format, unit_format)))))).

Definition SRS_PosResourceSet_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResourceSet_r16__ext_list.
Definition SRS_PosResourceSet_r16__ext_Format_list : SRS_PosResourceSet_r16__ext_Format_Type :=
  unit__Format.

Definition SRS_PosResourceSet_r16__list_type : Set := (seq_type SRS_PosResourceSet_r16__root_list) * (seq_ext_type SRS_PosResourceSet_r16__ext_list).
Definition SRS_PosResourceSet_r16__list_cond (z : SRS_PosResourceSet_r16__list_type) : Prop :=
        (seq_cond SRS_PosResourceSet_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResourceSet_r16__ext_list (snd z)).
Definition SRS_PosResourceSet_r16__list_format : T_Format SRS_PosResourceSet_r16__list_type SRS_PosResourceSet_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResourceSet_r16__root_list SRS_PosResourceSet_r16__root_Format_list SRS_PosResourceSet_r16__ext_list SRS_PosResourceSet_r16__ext_Format_list.

Opaque SRS_PosResourceSet_r16__list_format.
Definition SRS_PosResourceSet_r16__F1 (z : SRS_PosResourceSet_r16__Type) : SRS_PosResourceSet_r16__list_type :=
  (((SRS_PosResourceSet_r16__srs_PosResourceSetId_r16 z, (SRS_PosResourceSet_r16__srs_PosResourceIdList_r16 z, (SRS_PosResourceSet_r16__resourceType_r16 z, (SRS_PosResourceSet_r16__alpha_r16 z, (SRS_PosResourceSet_r16__p0_r16 z, (SRS_PosResourceSet_r16__pathlossReferenceRS_Pos_r16 z, tt))))))), (
tt)).
Definition SRS_PosResourceSet_r16__F2 (y : SRS_PosResourceSet_r16__list_type) : SRS_PosResourceSet_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__SRS_PosResourceSet_r16__Type j0 j1 j2 j3 j4 j5
  end.
Definition SRS_PosResourceSet_r16__helper1 : (forall a : SRS_PosResourceSet_r16__Type, SRS_PosResourceSet_r16__cond a -> SRS_PosResourceSet_r16__list_cond (SRS_PosResourceSet_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResourceSet_r16__helper2 : (forall a : SRS_PosResourceSet_r16__Type, SRS_PosResourceSet_r16__F2 (SRS_PosResourceSet_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResourceSet_r16__helper3 : (forall b : SRS_PosResourceSet_r16__list_type, SRS_PosResourceSet_r16__list_cond b -> SRS_PosResourceSet_r16__cond (SRS_PosResourceSet_r16__F2 b) /\ SRS_PosResourceSet_r16__F1 (SRS_PosResourceSet_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResourceSet_r16__cond, SRS_PosResourceSet_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResourceSet_r16__Format : T_Format SRS_PosResourceSet_r16__Type SRS_PosResourceSet_r16__cond :=
 proj2_format SRS_PosResourceSet_r16__cond SRS_PosResourceSet_r16__list_format  SRS_PosResourceSet_r16__F1 SRS_PosResourceSet_r16__F2 SRS_PosResourceSet_r16__helper1 SRS_PosResourceSet_r16__helper2 SRS_PosResourceSet_r16__helper3.

Opaque SRS_PosResourceSet_r16__cond SRS_PosResourceSet_r16__Format.

