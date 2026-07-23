Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_ConfigDedicatedNR_r16.

Opaque SL_ConfigDedicatedNR_r16__cond SL_ConfigDedicatedNR_r16__Format.

Require Import NR.SL_L2RemoteUE_Config_r17.

Opaque SL_L2RemoteUE_Config_r17__cond SL_L2RemoteUE_Config_r17__Format.

Record RRCSetup_v1700_IEs__nonCriticalExtension__Type : Set := make__RRCSetup_v1700_IEs__nonCriticalExtension__Type {}.
Definition RRCSetup_v1700_IEs__nonCriticalExtension__cond (z : RRCSetup_v1700_IEs__nonCriticalExtension__Type) := True.
Record RRCSetup_v1700_IEs__Type : Set :=
  make__RRCSetup_v1700_IEs__Type {
    RRCSetup_v1700_IEs__sl_ConfigDedicatedNR_r17 : option SL_ConfigDedicatedNR_r16__Type ;
    RRCSetup_v1700_IEs__sl_L2RemoteUE_Config_r17 : option SL_L2RemoteUE_Config_r17__Type ;
    RRCSetup_v1700_IEs__nonCriticalExtension : option RRCSetup_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition RRCSetup_v1700_IEs__list := (
 Opt SL_ConfigDedicatedNR_r16__Type SL_ConfigDedicatedNR_r16__cond ::
 Opt SL_L2RemoteUE_Config_r17__Type SL_L2RemoteUE_Config_r17__cond ::
 Opt RRCSetup_v1700_IEs__nonCriticalExtension__Type RRCSetup_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition RRCSetup_v1700_IEs__cond z := 
  opt_cond SL_ConfigDedicatedNR_r16__cond (RRCSetup_v1700_IEs__sl_ConfigDedicatedNR_r17 z) /\
  opt_cond SL_L2RemoteUE_Config_r17__cond (RRCSetup_v1700_IEs__sl_L2RemoteUE_Config_r17 z) /\
  opt_cond RRCSetup_v1700_IEs__nonCriticalExtension__cond (RRCSetup_v1700_IEs__nonCriticalExtension z) /\
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
Definition RRCSetup_v1700_IEs__nonCriticalExtension__helper : forall a : RRCSetup_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__RRCSetup_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCSetup_v1700_IEs__nonCriticalExtension__Format : T_Format RRCSetup_v1700_IEs__nonCriticalExtension__Type RRCSetup_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCSetup_v1700_IEs__nonCriticalExtension__Type)
    RRCSetup_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque RRCSetup_v1700_IEs__nonCriticalExtension__cond RRCSetup_v1700_IEs__nonCriticalExtension__Format.


Definition RRCSetup_v1700_IEs__Format_Type := Eval cbn in seq_format_prod RRCSetup_v1700_IEs__list.
Definition RRCSetup_v1700_IEs__Format_list : RRCSetup_v1700_IEs__Format_Type :=
  (SL_ConfigDedicatedNR_r16__Format, (SL_L2RemoteUE_Config_r17__Format, (RRCSetup_v1700_IEs__nonCriticalExtension__Format, unit_format))).
Definition RRCSetup_v1700_IEs__list__Format := (*Eval compute in *) seq_format RRCSetup_v1700_IEs__list RRCSetup_v1700_IEs__Format_list.
Definition RRCSetup_v1700_IEs__F1 z :=
  (RRCSetup_v1700_IEs__sl_ConfigDedicatedNR_r17 z, (RRCSetup_v1700_IEs__sl_L2RemoteUE_Config_r17 z, (RRCSetup_v1700_IEs__nonCriticalExtension z, tt))).
Definition RRCSetup_v1700_IEs__F2 (y : seq_type RRCSetup_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RRCSetup_v1700_IEs__Type i0 i1 i2
  end.
Lemma RRCSetup_v1700_IEs__F1F2_cond (z : RRCSetup_v1700_IEs__Type)
  : RRCSetup_v1700_IEs__cond z ->
  (seq_cond RRCSetup_v1700_IEs__list (RRCSetup_v1700_IEs__F1 z)).
intro H. unfold RRCSetup_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma RRCSetup_v1700_IEs__F1F2_cond2 (z : RRCSetup_v1700_IEs__Type)
 : RRCSetup_v1700_IEs__F2 (RRCSetup_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCSetup_v1700_IEs__F2F1_cond (y : seq_type RRCSetup_v1700_IEs__list)
  : seq_cond RRCSetup_v1700_IEs__list y ->
 (RRCSetup_v1700_IEs__cond (RRCSetup_v1700_IEs__F2 y)) /\  RRCSetup_v1700_IEs__F1 (RRCSetup_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCSetup_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCSetup_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCSetup_v1700_IEs__Format : T_Format RRCSetup_v1700_IEs__Type RRCSetup_v1700_IEs__cond :=
        proj2_format  RRCSetup_v1700_IEs__cond RRCSetup_v1700_IEs__list__Format
    RRCSetup_v1700_IEs__F1 RRCSetup_v1700_IEs__F2 RRCSetup_v1700_IEs__F1F2_cond  RRCSetup_v1700_IEs__F1F2_cond2 RRCSetup_v1700_IEs__F2F1_cond.
Opaque RRCSetup_v1700_IEs__cond RRCSetup_v1700_IEs__Format.

