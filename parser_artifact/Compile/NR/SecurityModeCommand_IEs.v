Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SecurityConfigSMC.

Opaque SecurityConfigSMC__cond SecurityConfigSMC__Format.

Record SecurityModeCommand_IEs__nonCriticalExtension__Type : Set := make__SecurityModeCommand_IEs__nonCriticalExtension__Type {}.
Definition SecurityModeCommand_IEs__nonCriticalExtension__cond (z : SecurityModeCommand_IEs__nonCriticalExtension__Type) := True.
Record SecurityModeCommand_IEs__Type : Set :=
  make__SecurityModeCommand_IEs__Type {
    SecurityModeCommand_IEs__securityConfigSMC : SecurityConfigSMC__Type ;
    SecurityModeCommand_IEs__lateNonCriticalExtension : option octet_string ;
    SecurityModeCommand_IEs__nonCriticalExtension : option SecurityModeCommand_IEs__nonCriticalExtension__Type ;
}.
Definition SecurityModeCommand_IEs__list := (
 Nor SecurityConfigSMC__Type SecurityConfigSMC__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SecurityModeCommand_IEs__nonCriticalExtension__Type SecurityModeCommand_IEs__nonCriticalExtension__cond ::
 nil).
Definition SecurityModeCommand_IEs__cond z := 
  SecurityConfigSMC__cond (SecurityModeCommand_IEs__securityConfigSMC z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SecurityModeCommand_IEs__lateNonCriticalExtension z) /\
  opt_cond SecurityModeCommand_IEs__nonCriticalExtension__cond (SecurityModeCommand_IEs__nonCriticalExtension z) /\
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
Definition SecurityModeCommand_IEs__nonCriticalExtension__helper : forall a : SecurityModeCommand_IEs__nonCriticalExtension__Type, True -> True /\ make__SecurityModeCommand_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition SecurityModeCommand_IEs__nonCriticalExtension__Format : T_Format SecurityModeCommand_IEs__nonCriticalExtension__Type SecurityModeCommand_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SecurityModeCommand_IEs__nonCriticalExtension__Type)
    SecurityModeCommand_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque SecurityModeCommand_IEs__nonCriticalExtension__cond SecurityModeCommand_IEs__nonCriticalExtension__Format.


Definition SecurityModeCommand_IEs__Format_Type := Eval cbn in seq_format_prod SecurityModeCommand_IEs__list.
Definition SecurityModeCommand_IEs__Format_list : SecurityModeCommand_IEs__Format_Type :=
  (SecurityConfigSMC__Format, (octet_string_nc__Format, (SecurityModeCommand_IEs__nonCriticalExtension__Format, unit_format))).
Definition SecurityModeCommand_IEs__list__Format := (*Eval compute in *) seq_format SecurityModeCommand_IEs__list SecurityModeCommand_IEs__Format_list.
Definition SecurityModeCommand_IEs__F1 z :=
  (SecurityModeCommand_IEs__securityConfigSMC z, (SecurityModeCommand_IEs__lateNonCriticalExtension z, (SecurityModeCommand_IEs__nonCriticalExtension z, tt))).
Definition SecurityModeCommand_IEs__F2 (y : seq_type SecurityModeCommand_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SecurityModeCommand_IEs__Type i0 i1 i2
  end.
Lemma SecurityModeCommand_IEs__F1F2_cond (z : SecurityModeCommand_IEs__Type)
  : SecurityModeCommand_IEs__cond z ->
  (seq_cond SecurityModeCommand_IEs__list (SecurityModeCommand_IEs__F1 z)).
intro H. unfold SecurityModeCommand_IEs__cond in H. simpl. auto. Qed.
Lemma SecurityModeCommand_IEs__F1F2_cond2 (z : SecurityModeCommand_IEs__Type)
 : SecurityModeCommand_IEs__F2 (SecurityModeCommand_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SecurityModeCommand_IEs__F2F1_cond (y : seq_type SecurityModeCommand_IEs__list)
  : seq_cond SecurityModeCommand_IEs__list y ->
 (SecurityModeCommand_IEs__cond (SecurityModeCommand_IEs__F2 y)) /\  SecurityModeCommand_IEs__F1 (SecurityModeCommand_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SecurityModeCommand_IEs__cond. simpl in *. auto.
 - simpl. unfold SecurityModeCommand_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SecurityModeCommand_IEs__Format : T_Format SecurityModeCommand_IEs__Type SecurityModeCommand_IEs__cond :=
        proj2_format  SecurityModeCommand_IEs__cond SecurityModeCommand_IEs__list__Format
    SecurityModeCommand_IEs__F1 SecurityModeCommand_IEs__F2 SecurityModeCommand_IEs__F1F2_cond  SecurityModeCommand_IEs__F1F2_cond2 SecurityModeCommand_IEs__F2F1_cond.
Opaque SecurityModeCommand_IEs__cond SecurityModeCommand_IEs__Format.

