Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasAndMobParametersMRDC_v1730.

Opaque MeasAndMobParametersMRDC_v1730__cond MeasAndMobParametersMRDC_v1730__Format.

Record UE_MRDC_Capability_v1730__nonCriticalExtension__Type : Set := make__UE_MRDC_Capability_v1730__nonCriticalExtension__Type {}.
Definition UE_MRDC_Capability_v1730__nonCriticalExtension__cond (z : UE_MRDC_Capability_v1730__nonCriticalExtension__Type) := True.
Record UE_MRDC_Capability_v1730__Type : Set :=
  make__UE_MRDC_Capability_v1730__Type {
    UE_MRDC_Capability_v1730__measAndMobParametersMRDC_v1730 : option MeasAndMobParametersMRDC_v1730__Type ;
    UE_MRDC_Capability_v1730__nonCriticalExtension : option UE_MRDC_Capability_v1730__nonCriticalExtension__Type ;
}.
Definition UE_MRDC_Capability_v1730__list := (
 Opt MeasAndMobParametersMRDC_v1730__Type MeasAndMobParametersMRDC_v1730__cond ::
 Opt UE_MRDC_Capability_v1730__nonCriticalExtension__Type UE_MRDC_Capability_v1730__nonCriticalExtension__cond ::
 nil).
Definition UE_MRDC_Capability_v1730__cond z := 
  opt_cond MeasAndMobParametersMRDC_v1730__cond (UE_MRDC_Capability_v1730__measAndMobParametersMRDC_v1730 z) /\
  opt_cond UE_MRDC_Capability_v1730__nonCriticalExtension__cond (UE_MRDC_Capability_v1730__nonCriticalExtension z) /\
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
Definition UE_MRDC_Capability_v1730__nonCriticalExtension__helper : forall a : UE_MRDC_Capability_v1730__nonCriticalExtension__Type, True -> True /\ make__UE_MRDC_Capability_v1730__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UE_MRDC_Capability_v1730__nonCriticalExtension__Format : T_Format UE_MRDC_Capability_v1730__nonCriticalExtension__Type UE_MRDC_Capability_v1730__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UE_MRDC_Capability_v1730__nonCriticalExtension__Type)
    UE_MRDC_Capability_v1730__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque UE_MRDC_Capability_v1730__nonCriticalExtension__cond UE_MRDC_Capability_v1730__nonCriticalExtension__Format.


Definition UE_MRDC_Capability_v1730__Format_Type := Eval cbn in seq_format_prod UE_MRDC_Capability_v1730__list.
Definition UE_MRDC_Capability_v1730__Format_list : UE_MRDC_Capability_v1730__Format_Type :=
  (MeasAndMobParametersMRDC_v1730__Format, (UE_MRDC_Capability_v1730__nonCriticalExtension__Format, unit_format)).
Definition UE_MRDC_Capability_v1730__list__Format := (*Eval compute in *) seq_format UE_MRDC_Capability_v1730__list UE_MRDC_Capability_v1730__Format_list.
Definition UE_MRDC_Capability_v1730__F1 z :=
  (UE_MRDC_Capability_v1730__measAndMobParametersMRDC_v1730 z, (UE_MRDC_Capability_v1730__nonCriticalExtension z, tt)).
Definition UE_MRDC_Capability_v1730__F2 (y : seq_type UE_MRDC_Capability_v1730__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UE_MRDC_Capability_v1730__Type i0 i1
  end.
Lemma UE_MRDC_Capability_v1730__F1F2_cond (z : UE_MRDC_Capability_v1730__Type)
  : UE_MRDC_Capability_v1730__cond z ->
  (seq_cond UE_MRDC_Capability_v1730__list (UE_MRDC_Capability_v1730__F1 z)).
intro H. unfold UE_MRDC_Capability_v1730__cond in H. simpl. auto. Qed.
Lemma UE_MRDC_Capability_v1730__F1F2_cond2 (z : UE_MRDC_Capability_v1730__Type)
 : UE_MRDC_Capability_v1730__F2 (UE_MRDC_Capability_v1730__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_MRDC_Capability_v1730__F2F1_cond (y : seq_type UE_MRDC_Capability_v1730__list)
  : seq_cond UE_MRDC_Capability_v1730__list y ->
 (UE_MRDC_Capability_v1730__cond (UE_MRDC_Capability_v1730__F2 y)) /\  UE_MRDC_Capability_v1730__F1 (UE_MRDC_Capability_v1730__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_MRDC_Capability_v1730__cond. simpl in *. auto.
 - simpl. unfold UE_MRDC_Capability_v1730__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_MRDC_Capability_v1730__Format : T_Format UE_MRDC_Capability_v1730__Type UE_MRDC_Capability_v1730__cond :=
        proj2_format  UE_MRDC_Capability_v1730__cond UE_MRDC_Capability_v1730__list__Format
    UE_MRDC_Capability_v1730__F1 UE_MRDC_Capability_v1730__F2 UE_MRDC_Capability_v1730__F1F2_cond  UE_MRDC_Capability_v1730__F1F2_cond2 UE_MRDC_Capability_v1730__F2F1_cond.
Opaque UE_MRDC_Capability_v1730__cond UE_MRDC_Capability_v1730__Format.

