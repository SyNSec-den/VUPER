Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.MAC_ParametersSidelink_r17.

Opaque MAC_ParametersSidelink_r17__cond MAC_ParametersSidelink_r17__Format.

Require Import NR.BandCombinationListSidelinkNR_v1710.

Opaque BandCombinationListSidelinkNR_v1710__cond BandCombinationListSidelinkNR_v1710__Format.

Record UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type : Set := make__UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type {}.
Definition UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__cond (z : UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type) := True.
Record UECapabilityInformationSidelink_v1700_IEs__Type : Set :=
  make__UECapabilityInformationSidelink_v1700_IEs__Type {
    UECapabilityInformationSidelink_v1700_IEs__mac_ParametersSidelink_r17 : option MAC_ParametersSidelink_r17__Type ;
    UECapabilityInformationSidelink_v1700_IEs__supportedBandCombinationListSidelinkNR_v1710 : option BandCombinationListSidelinkNR_v1710__Type ;
    UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension : option UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition UECapabilityInformationSidelink_v1700_IEs__list := (
 Opt MAC_ParametersSidelink_r17__Type MAC_ParametersSidelink_r17__cond ::
 Opt BandCombinationListSidelinkNR_v1710__Type BandCombinationListSidelinkNR_v1710__cond ::
 Opt UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition UECapabilityInformationSidelink_v1700_IEs__cond z := 
  opt_cond MAC_ParametersSidelink_r17__cond (UECapabilityInformationSidelink_v1700_IEs__mac_ParametersSidelink_r17 z) /\
  opt_cond BandCombinationListSidelinkNR_v1710__cond (UECapabilityInformationSidelink_v1700_IEs__supportedBandCombinationListSidelinkNR_v1710 z) /\
  opt_cond UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__cond (UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension z) /\
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
Definition UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__helper : forall a : UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Format : T_Format UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Type)
    UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__cond UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Format.


Definition UECapabilityInformationSidelink_v1700_IEs__Format_Type := Eval cbn in seq_format_prod UECapabilityInformationSidelink_v1700_IEs__list.
Definition UECapabilityInformationSidelink_v1700_IEs__Format_list : UECapabilityInformationSidelink_v1700_IEs__Format_Type :=
  (MAC_ParametersSidelink_r17__Format, (BandCombinationListSidelinkNR_v1710__Format, (UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension__Format, unit_format))).
Definition UECapabilityInformationSidelink_v1700_IEs__list__Format := (*Eval compute in *) seq_format UECapabilityInformationSidelink_v1700_IEs__list UECapabilityInformationSidelink_v1700_IEs__Format_list.
Definition UECapabilityInformationSidelink_v1700_IEs__F1 z :=
  (UECapabilityInformationSidelink_v1700_IEs__mac_ParametersSidelink_r17 z, (UECapabilityInformationSidelink_v1700_IEs__supportedBandCombinationListSidelinkNR_v1710 z, (UECapabilityInformationSidelink_v1700_IEs__nonCriticalExtension z, tt))).
Definition UECapabilityInformationSidelink_v1700_IEs__F2 (y : seq_type UECapabilityInformationSidelink_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UECapabilityInformationSidelink_v1700_IEs__Type i0 i1 i2
  end.
Lemma UECapabilityInformationSidelink_v1700_IEs__F1F2_cond (z : UECapabilityInformationSidelink_v1700_IEs__Type)
  : UECapabilityInformationSidelink_v1700_IEs__cond z ->
  (seq_cond UECapabilityInformationSidelink_v1700_IEs__list (UECapabilityInformationSidelink_v1700_IEs__F1 z)).
intro H. unfold UECapabilityInformationSidelink_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma UECapabilityInformationSidelink_v1700_IEs__F1F2_cond2 (z : UECapabilityInformationSidelink_v1700_IEs__Type)
 : UECapabilityInformationSidelink_v1700_IEs__F2 (UECapabilityInformationSidelink_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UECapabilityInformationSidelink_v1700_IEs__F2F1_cond (y : seq_type UECapabilityInformationSidelink_v1700_IEs__list)
  : seq_cond UECapabilityInformationSidelink_v1700_IEs__list y ->
 (UECapabilityInformationSidelink_v1700_IEs__cond (UECapabilityInformationSidelink_v1700_IEs__F2 y)) /\  UECapabilityInformationSidelink_v1700_IEs__F1 (UECapabilityInformationSidelink_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UECapabilityInformationSidelink_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold UECapabilityInformationSidelink_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UECapabilityInformationSidelink_v1700_IEs__Format : T_Format UECapabilityInformationSidelink_v1700_IEs__Type UECapabilityInformationSidelink_v1700_IEs__cond :=
        proj2_format  UECapabilityInformationSidelink_v1700_IEs__cond UECapabilityInformationSidelink_v1700_IEs__list__Format
    UECapabilityInformationSidelink_v1700_IEs__F1 UECapabilityInformationSidelink_v1700_IEs__F2 UECapabilityInformationSidelink_v1700_IEs__F1F2_cond  UECapabilityInformationSidelink_v1700_IEs__F1F2_cond2 UECapabilityInformationSidelink_v1700_IEs__F2F1_cond.
Opaque UECapabilityInformationSidelink_v1700_IEs__cond UECapabilityInformationSidelink_v1700_IEs__Format.

