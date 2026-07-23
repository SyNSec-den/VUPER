Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SCellActivationRS_ConfigId_r17.

Opaque SCellActivationRS_ConfigId_r17__cond SCellActivationRS_ConfigId_r17__Format.

Require Import NR.NZP_CSI_RS_ResourceSetId.

Opaque NZP_CSI_RS_ResourceSetId__cond NZP_CSI_RS_ResourceSetId__Format.

Lemma SCellActivationRS_Config_r17__gapBetweenBursts_r17__helper1 : (2 <= 31)%Z.  lia. Qed.
Lemma SCellActivationRS_Config_r17__gapBetweenBursts_r17__helper2 : to_bit_sz (Z.to_nat (31 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply SCellActivationRS_Config_r17__gapBetweenBursts_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SCellActivationRS_Config_r17__gapBetweenBursts_r17__Type := Z.
Definition SCellActivationRS_Config_r17__gapBetweenBursts_r17__cond := (fun z => (2 <= z <= 31)%Z).
Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Record SCellActivationRS_Config_r17__Type : Set :=
  make__SCellActivationRS_Config_r17__Type {
    SCellActivationRS_Config_r17__scellActivationRS_Id_r17 : SCellActivationRS_ConfigId_r17__Type ;
    SCellActivationRS_Config_r17__resourceSet_r17 : NZP_CSI_RS_ResourceSetId__Type ;
    SCellActivationRS_Config_r17__gapBetweenBursts_r17 : option Z ;
    SCellActivationRS_Config_r17__qcl_Info_r17 : TCI_StateId__Type ;
}.
Definition SCellActivationRS_Config_r17__root_list : list seq_elem := (
 Nor SCellActivationRS_ConfigId_r17__Type SCellActivationRS_ConfigId_r17__cond ::
 Nor NZP_CSI_RS_ResourceSetId__Type NZP_CSI_RS_ResourceSetId__cond ::
 Opt Z SCellActivationRS_Config_r17__gapBetweenBursts_r17__cond ::
 Nor TCI_StateId__Type TCI_StateId__cond ::
 nil).
Definition SCellActivationRS_Config_r17__ext_list : list typ := (
  nil).
Definition SCellActivationRS_Config_r17__cond (z : SCellActivationRS_Config_r17__Type) := 
(  SCellActivationRS_ConfigId_r17__cond (SCellActivationRS_Config_r17__scellActivationRS_Id_r17 z) /\
  NZP_CSI_RS_ResourceSetId__cond (SCellActivationRS_Config_r17__resourceSet_r17 z) /\
  opt_cond SCellActivationRS_Config_r17__gapBetweenBursts_r17__cond (SCellActivationRS_Config_r17__gapBetweenBursts_r17 z) /\
  TCI_StateId__cond (SCellActivationRS_Config_r17__qcl_Info_r17 z) /\
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
Definition SCellActivationRS_Config_r17__gapBetweenBursts_r17__Format : T_Format Z SCellActivationRS_Config_r17__gapBetweenBursts_r17__cond :=
 ranged_int_format (2) (31) SCellActivationRS_Config_r17__gapBetweenBursts_r17__helper1 SCellActivationRS_Config_r17__gapBetweenBursts_r17__helper2.

Opaque SCellActivationRS_Config_r17__gapBetweenBursts_r17__cond SCellActivationRS_Config_r17__gapBetweenBursts_r17__Format.


Definition SCellActivationRS_Config_r17__root_Format_Type := Eval cbn in seq_format_prod SCellActivationRS_Config_r17__root_list.
Definition SCellActivationRS_Config_r17__root_Format_list : SCellActivationRS_Config_r17__root_Format_Type :=
  (SCellActivationRS_ConfigId_r17__Format, (NZP_CSI_RS_ResourceSetId__Format, (SCellActivationRS_Config_r17__gapBetweenBursts_r17__Format, (TCI_StateId__Format, unit_format)))).

Definition SCellActivationRS_Config_r17__ext_Format_Type := Eval cbn in get_formats SCellActivationRS_Config_r17__ext_list.
Definition SCellActivationRS_Config_r17__ext_Format_list : SCellActivationRS_Config_r17__ext_Format_Type :=
  unit__Format.

Definition SCellActivationRS_Config_r17__list_type : Set := (seq_type SCellActivationRS_Config_r17__root_list) * (seq_ext_type SCellActivationRS_Config_r17__ext_list).
Definition SCellActivationRS_Config_r17__list_cond (z : SCellActivationRS_Config_r17__list_type) : Prop :=
        (seq_cond SCellActivationRS_Config_r17__root_list (fst z)) /\ (seq_ext_cond SCellActivationRS_Config_r17__ext_list (snd z)).
Definition SCellActivationRS_Config_r17__list_format : T_Format SCellActivationRS_Config_r17__list_type SCellActivationRS_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SCellActivationRS_Config_r17__root_list SCellActivationRS_Config_r17__root_Format_list SCellActivationRS_Config_r17__ext_list SCellActivationRS_Config_r17__ext_Format_list.

Opaque SCellActivationRS_Config_r17__list_format.
Definition SCellActivationRS_Config_r17__F1 (z : SCellActivationRS_Config_r17__Type) : SCellActivationRS_Config_r17__list_type :=
  (((SCellActivationRS_Config_r17__scellActivationRS_Id_r17 z, (SCellActivationRS_Config_r17__resourceSet_r17 z, (SCellActivationRS_Config_r17__gapBetweenBursts_r17 z, (SCellActivationRS_Config_r17__qcl_Info_r17 z, tt))))), (
tt)).
Definition SCellActivationRS_Config_r17__F2 (y : SCellActivationRS_Config_r17__list_type) : SCellActivationRS_Config_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SCellActivationRS_Config_r17__Type j0 j1 j2 j3
  end.
Definition SCellActivationRS_Config_r17__helper1 : (forall a : SCellActivationRS_Config_r17__Type, SCellActivationRS_Config_r17__cond a -> SCellActivationRS_Config_r17__list_cond (SCellActivationRS_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SCellActivationRS_Config_r17__helper2 : (forall a : SCellActivationRS_Config_r17__Type, SCellActivationRS_Config_r17__F2 (SCellActivationRS_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SCellActivationRS_Config_r17__helper3 : (forall b : SCellActivationRS_Config_r17__list_type, SCellActivationRS_Config_r17__list_cond b -> SCellActivationRS_Config_r17__cond (SCellActivationRS_Config_r17__F2 b) /\ SCellActivationRS_Config_r17__F1 (SCellActivationRS_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SCellActivationRS_Config_r17__cond, SCellActivationRS_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SCellActivationRS_Config_r17__Format : T_Format SCellActivationRS_Config_r17__Type SCellActivationRS_Config_r17__cond :=
 proj2_format SCellActivationRS_Config_r17__cond SCellActivationRS_Config_r17__list_format  SCellActivationRS_Config_r17__F1 SCellActivationRS_Config_r17__F2 SCellActivationRS_Config_r17__helper1 SCellActivationRS_Config_r17__helper2 SCellActivationRS_Config_r17__helper3.

Opaque SCellActivationRS_Config_r17__cond SCellActivationRS_Config_r17__Format.

