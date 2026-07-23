Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSSI_ResourceId_r16.

Opaque RSSI_ResourceId_r16__cond RSSI_ResourceId_r16__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Lemma RSSI_ResourceConfigCLI_r16__startPRB_r16__helper1 : (0 <= 2169)%Z.  lia. Qed.
Lemma RSSI_ResourceConfigCLI_r16__startPRB_r16__helper2 : to_bit_sz (Z.to_nat (2169 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2169 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_ResourceConfigCLI_r16__startPRB_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_ResourceConfigCLI_r16__startPRB_r16__Type := Z.
Definition RSSI_ResourceConfigCLI_r16__startPRB_r16__cond := (fun z => (0 <= z <= 2169)%Z).
Lemma RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__helper1 : (4 <= maxNrofPhysicalResourceBlocksPlus1)%Z. unfold maxNrofPhysicalResourceBlocksPlus1.
 lia. Qed.
Lemma RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocksPlus1 - 4)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocksPlus1 - 4))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__Type := Z.
Definition RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__cond := (fun z => (4 <= z <= maxNrofPhysicalResourceBlocksPlus1)%Z).
Lemma RSSI_ResourceConfigCLI_r16__startPosition_r16__helper1 : (0 <= 13)%Z.  lia. Qed.
Lemma RSSI_ResourceConfigCLI_r16__startPosition_r16__helper2 : to_bit_sz (Z.to_nat (13 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (13 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_ResourceConfigCLI_r16__startPosition_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_ResourceConfigCLI_r16__startPosition_r16__Type := Z.
Definition RSSI_ResourceConfigCLI_r16__startPosition_r16__cond := (fun z => (0 <= z <= 13)%Z).
Lemma RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__helper1 : (1 <= 14)%Z.  lia. Qed.
Lemma RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__helper2 : to_bit_sz (Z.to_nat (14 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (14 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__Type := Z.
Definition RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__cond := (fun z => (1 <= z <= 14)%Z).
Require Import NR.RSSI_PeriodicityAndOffset_r16.

Opaque RSSI_PeriodicityAndOffset_r16__cond RSSI_PeriodicityAndOffset_r16__Format.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Record RSSI_ResourceConfigCLI_r16__Type : Set :=
  make__RSSI_ResourceConfigCLI_r16__Type {
    RSSI_ResourceConfigCLI_r16__rssi_ResourceId_r16 : RSSI_ResourceId_r16__Type ;
    RSSI_ResourceConfigCLI_r16__rssi_SCS_r16 : SubcarrierSpacing__Type ;
    RSSI_ResourceConfigCLI_r16__startPRB_r16 : Z ;
    RSSI_ResourceConfigCLI_r16__nrofPRBs_r16 : Z ;
    RSSI_ResourceConfigCLI_r16__startPosition_r16 : Z ;
    RSSI_ResourceConfigCLI_r16__nrofSymbols_r16 : Z ;
    RSSI_ResourceConfigCLI_r16__rssi_PeriodicityAndOffset_r16 : RSSI_PeriodicityAndOffset_r16__Type ;
    RSSI_ResourceConfigCLI_r16__refServCellIndex_r16 : option ServCellIndex__Type ;
}.
Definition RSSI_ResourceConfigCLI_r16__root_list : list seq_elem := (
 Nor RSSI_ResourceId_r16__Type RSSI_ResourceId_r16__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor Z RSSI_ResourceConfigCLI_r16__startPRB_r16__cond ::
 Nor Z RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__cond ::
 Nor Z RSSI_ResourceConfigCLI_r16__startPosition_r16__cond ::
 Nor Z RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__cond ::
 Nor RSSI_PeriodicityAndOffset_r16__Type RSSI_PeriodicityAndOffset_r16__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 nil).
Definition RSSI_ResourceConfigCLI_r16__ext_list : list typ := (
  nil).
Definition RSSI_ResourceConfigCLI_r16__cond (z : RSSI_ResourceConfigCLI_r16__Type) := 
(  RSSI_ResourceId_r16__cond (RSSI_ResourceConfigCLI_r16__rssi_ResourceId_r16 z) /\
  SubcarrierSpacing__cond (RSSI_ResourceConfigCLI_r16__rssi_SCS_r16 z) /\
  RSSI_ResourceConfigCLI_r16__startPRB_r16__cond (RSSI_ResourceConfigCLI_r16__startPRB_r16 z) /\
  RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__cond (RSSI_ResourceConfigCLI_r16__nrofPRBs_r16 z) /\
  RSSI_ResourceConfigCLI_r16__startPosition_r16__cond (RSSI_ResourceConfigCLI_r16__startPosition_r16 z) /\
  RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__cond (RSSI_ResourceConfigCLI_r16__nrofSymbols_r16 z) /\
  RSSI_PeriodicityAndOffset_r16__cond (RSSI_ResourceConfigCLI_r16__rssi_PeriodicityAndOffset_r16 z) /\
  opt_cond ServCellIndex__cond (RSSI_ResourceConfigCLI_r16__refServCellIndex_r16 z) /\
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
Definition RSSI_ResourceConfigCLI_r16__startPRB_r16__Format : T_Format Z RSSI_ResourceConfigCLI_r16__startPRB_r16__cond :=
 ranged_int_format (0) (2169) RSSI_ResourceConfigCLI_r16__startPRB_r16__helper1 RSSI_ResourceConfigCLI_r16__startPRB_r16__helper2.

Opaque RSSI_ResourceConfigCLI_r16__startPRB_r16__cond RSSI_ResourceConfigCLI_r16__startPRB_r16__Format.

Definition RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__Format : T_Format Z RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__cond :=
 ranged_int_format (4) (maxNrofPhysicalResourceBlocksPlus1) RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__helper1 RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__helper2.

Opaque RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__cond RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__Format.

Definition RSSI_ResourceConfigCLI_r16__startPosition_r16__Format : T_Format Z RSSI_ResourceConfigCLI_r16__startPosition_r16__cond :=
 ranged_int_format (0) (13) RSSI_ResourceConfigCLI_r16__startPosition_r16__helper1 RSSI_ResourceConfigCLI_r16__startPosition_r16__helper2.

Opaque RSSI_ResourceConfigCLI_r16__startPosition_r16__cond RSSI_ResourceConfigCLI_r16__startPosition_r16__Format.

Definition RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__Format : T_Format Z RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__cond :=
 ranged_int_format (1) (14) RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__helper1 RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__helper2.

Opaque RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__cond RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__Format.


Definition RSSI_ResourceConfigCLI_r16__root_Format_Type := Eval cbn in seq_format_prod RSSI_ResourceConfigCLI_r16__root_list.
Definition RSSI_ResourceConfigCLI_r16__root_Format_list : RSSI_ResourceConfigCLI_r16__root_Format_Type :=
  (RSSI_ResourceId_r16__Format, (SubcarrierSpacing__Format, (RSSI_ResourceConfigCLI_r16__startPRB_r16__Format, (RSSI_ResourceConfigCLI_r16__nrofPRBs_r16__Format, (RSSI_ResourceConfigCLI_r16__startPosition_r16__Format, (RSSI_ResourceConfigCLI_r16__nrofSymbols_r16__Format, (RSSI_PeriodicityAndOffset_r16__Format, (ServCellIndex__Format, unit_format)))))))).

Definition RSSI_ResourceConfigCLI_r16__ext_Format_Type := Eval cbn in get_formats RSSI_ResourceConfigCLI_r16__ext_list.
Definition RSSI_ResourceConfigCLI_r16__ext_Format_list : RSSI_ResourceConfigCLI_r16__ext_Format_Type :=
  unit__Format.

Definition RSSI_ResourceConfigCLI_r16__list_type : Set := (seq_type RSSI_ResourceConfigCLI_r16__root_list) * (seq_ext_type RSSI_ResourceConfigCLI_r16__ext_list).
Definition RSSI_ResourceConfigCLI_r16__list_cond (z : RSSI_ResourceConfigCLI_r16__list_type) : Prop :=
        (seq_cond RSSI_ResourceConfigCLI_r16__root_list (fst z)) /\ (seq_ext_cond RSSI_ResourceConfigCLI_r16__ext_list (snd z)).
Definition RSSI_ResourceConfigCLI_r16__list_format : T_Format RSSI_ResourceConfigCLI_r16__list_type RSSI_ResourceConfigCLI_r16__list_cond :=
 (* Eval compute in *) seq_ext_format RSSI_ResourceConfigCLI_r16__root_list RSSI_ResourceConfigCLI_r16__root_Format_list RSSI_ResourceConfigCLI_r16__ext_list RSSI_ResourceConfigCLI_r16__ext_Format_list.

Opaque RSSI_ResourceConfigCLI_r16__list_format.
Definition RSSI_ResourceConfigCLI_r16__F1 (z : RSSI_ResourceConfigCLI_r16__Type) : RSSI_ResourceConfigCLI_r16__list_type :=
  (((RSSI_ResourceConfigCLI_r16__rssi_ResourceId_r16 z, (RSSI_ResourceConfigCLI_r16__rssi_SCS_r16 z, (RSSI_ResourceConfigCLI_r16__startPRB_r16 z, (RSSI_ResourceConfigCLI_r16__nrofPRBs_r16 z, (RSSI_ResourceConfigCLI_r16__startPosition_r16 z, (RSSI_ResourceConfigCLI_r16__nrofSymbols_r16 z, (RSSI_ResourceConfigCLI_r16__rssi_PeriodicityAndOffset_r16 z, (RSSI_ResourceConfigCLI_r16__refServCellIndex_r16 z, tt))))))))), (
tt)).
Definition RSSI_ResourceConfigCLI_r16__F2 (y : RSSI_ResourceConfigCLI_r16__list_type) : RSSI_ResourceConfigCLI_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), _)=>
    make__RSSI_ResourceConfigCLI_r16__Type j0 j1 j2 j3 j4 j5 j6 j7
  end.
Definition RSSI_ResourceConfigCLI_r16__helper1 : (forall a : RSSI_ResourceConfigCLI_r16__Type, RSSI_ResourceConfigCLI_r16__cond a -> RSSI_ResourceConfigCLI_r16__list_cond (RSSI_ResourceConfigCLI_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RSSI_ResourceConfigCLI_r16__helper2 : (forall a : RSSI_ResourceConfigCLI_r16__Type, RSSI_ResourceConfigCLI_r16__F2 (RSSI_ResourceConfigCLI_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RSSI_ResourceConfigCLI_r16__helper3 : (forall b : RSSI_ResourceConfigCLI_r16__list_type, RSSI_ResourceConfigCLI_r16__list_cond b -> RSSI_ResourceConfigCLI_r16__cond (RSSI_ResourceConfigCLI_r16__F2 b) /\ RSSI_ResourceConfigCLI_r16__F1 (RSSI_ResourceConfigCLI_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RSSI_ResourceConfigCLI_r16__cond, RSSI_ResourceConfigCLI_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RSSI_ResourceConfigCLI_r16__Format : T_Format RSSI_ResourceConfigCLI_r16__Type RSSI_ResourceConfigCLI_r16__cond :=
 proj2_format RSSI_ResourceConfigCLI_r16__cond RSSI_ResourceConfigCLI_r16__list_format  RSSI_ResourceConfigCLI_r16__F1 RSSI_ResourceConfigCLI_r16__F2 RSSI_ResourceConfigCLI_r16__helper1 RSSI_ResourceConfigCLI_r16__helper2 RSSI_ResourceConfigCLI_r16__helper3.

Opaque RSSI_ResourceConfigCLI_r16__cond RSSI_ResourceConfigCLI_r16__Format.

