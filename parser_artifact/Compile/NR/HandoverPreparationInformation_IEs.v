Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.UE_CapabilityRAT_ContainerList.

Opaque UE_CapabilityRAT_ContainerList__cond UE_CapabilityRAT_ContainerList__Format.

Require Import NR.AS_Config.

Opaque AS_Config__cond AS_Config__Format.

Require Import NR.RRM_Config.

Opaque RRM_Config__cond RRM_Config__Format.

Require Import NR.AS_Context.

Opaque AS_Context__cond AS_Context__Format.

Record HandoverPreparationInformation_IEs__nonCriticalExtension__Type : Set := make__HandoverPreparationInformation_IEs__nonCriticalExtension__Type {}.
Definition HandoverPreparationInformation_IEs__nonCriticalExtension__cond (z : HandoverPreparationInformation_IEs__nonCriticalExtension__Type) := True.
Record HandoverPreparationInformation_IEs__Type : Set :=
  make__HandoverPreparationInformation_IEs__Type {
    HandoverPreparationInformation_IEs__ue_CapabilityRAT_List : UE_CapabilityRAT_ContainerList__Type ;
    HandoverPreparationInformation_IEs__sourceConfig : option AS_Config__Type ;
    HandoverPreparationInformation_IEs__rrm_Config : option RRM_Config__Type ;
    HandoverPreparationInformation_IEs__as_Context : option AS_Context__Type ;
    HandoverPreparationInformation_IEs__nonCriticalExtension : option HandoverPreparationInformation_IEs__nonCriticalExtension__Type ;
}.
Definition HandoverPreparationInformation_IEs__list := (
 Nor UE_CapabilityRAT_ContainerList__Type UE_CapabilityRAT_ContainerList__cond ::
 Opt AS_Config__Type AS_Config__cond ::
 Opt RRM_Config__Type RRM_Config__cond ::
 Opt AS_Context__Type AS_Context__cond ::
 Opt HandoverPreparationInformation_IEs__nonCriticalExtension__Type HandoverPreparationInformation_IEs__nonCriticalExtension__cond ::
 nil).
Definition HandoverPreparationInformation_IEs__cond z := 
  UE_CapabilityRAT_ContainerList__cond (HandoverPreparationInformation_IEs__ue_CapabilityRAT_List z) /\
  opt_cond AS_Config__cond (HandoverPreparationInformation_IEs__sourceConfig z) /\
  opt_cond RRM_Config__cond (HandoverPreparationInformation_IEs__rrm_Config z) /\
  opt_cond AS_Context__cond (HandoverPreparationInformation_IEs__as_Context z) /\
  opt_cond HandoverPreparationInformation_IEs__nonCriticalExtension__cond (HandoverPreparationInformation_IEs__nonCriticalExtension z) /\
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
Definition HandoverPreparationInformation_IEs__nonCriticalExtension__helper : forall a : HandoverPreparationInformation_IEs__nonCriticalExtension__Type, True -> True /\ make__HandoverPreparationInformation_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition HandoverPreparationInformation_IEs__nonCriticalExtension__Format : T_Format HandoverPreparationInformation_IEs__nonCriticalExtension__Type HandoverPreparationInformation_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__HandoverPreparationInformation_IEs__nonCriticalExtension__Type)
    HandoverPreparationInformation_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque HandoverPreparationInformation_IEs__nonCriticalExtension__cond HandoverPreparationInformation_IEs__nonCriticalExtension__Format.


Definition HandoverPreparationInformation_IEs__Format_Type := Eval cbn in seq_format_prod HandoverPreparationInformation_IEs__list.
Definition HandoverPreparationInformation_IEs__Format_list : HandoverPreparationInformation_IEs__Format_Type :=
  (UE_CapabilityRAT_ContainerList__Format, (AS_Config__Format, (RRM_Config__Format, (AS_Context__Format, (HandoverPreparationInformation_IEs__nonCriticalExtension__Format, unit_format))))).
Definition HandoverPreparationInformation_IEs__list__Format := (*Eval compute in *) seq_format HandoverPreparationInformation_IEs__list HandoverPreparationInformation_IEs__Format_list.
Definition HandoverPreparationInformation_IEs__F1 z :=
  (HandoverPreparationInformation_IEs__ue_CapabilityRAT_List z, (HandoverPreparationInformation_IEs__sourceConfig z, (HandoverPreparationInformation_IEs__rrm_Config z, (HandoverPreparationInformation_IEs__as_Context z, (HandoverPreparationInformation_IEs__nonCriticalExtension z, tt))))).
Definition HandoverPreparationInformation_IEs__F2 (y : seq_type HandoverPreparationInformation_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__HandoverPreparationInformation_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma HandoverPreparationInformation_IEs__F1F2_cond (z : HandoverPreparationInformation_IEs__Type)
  : HandoverPreparationInformation_IEs__cond z ->
  (seq_cond HandoverPreparationInformation_IEs__list (HandoverPreparationInformation_IEs__F1 z)).
intro H. unfold HandoverPreparationInformation_IEs__cond in H. simpl. auto. Qed.
Lemma HandoverPreparationInformation_IEs__F1F2_cond2 (z : HandoverPreparationInformation_IEs__Type)
 : HandoverPreparationInformation_IEs__F2 (HandoverPreparationInformation_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma HandoverPreparationInformation_IEs__F2F1_cond (y : seq_type HandoverPreparationInformation_IEs__list)
  : seq_cond HandoverPreparationInformation_IEs__list y ->
 (HandoverPreparationInformation_IEs__cond (HandoverPreparationInformation_IEs__F2 y)) /\  HandoverPreparationInformation_IEs__F1 (HandoverPreparationInformation_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold HandoverPreparationInformation_IEs__cond. simpl in *. auto.
 - simpl. unfold HandoverPreparationInformation_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition HandoverPreparationInformation_IEs__Format : T_Format HandoverPreparationInformation_IEs__Type HandoverPreparationInformation_IEs__cond :=
        proj2_format  HandoverPreparationInformation_IEs__cond HandoverPreparationInformation_IEs__list__Format
    HandoverPreparationInformation_IEs__F1 HandoverPreparationInformation_IEs__F2 HandoverPreparationInformation_IEs__F1F2_cond  HandoverPreparationInformation_IEs__F1F2_cond2 HandoverPreparationInformation_IEs__F2F1_cond.
Opaque HandoverPreparationInformation_IEs__cond HandoverPreparationInformation_IEs__Format.

