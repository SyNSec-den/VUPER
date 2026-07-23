Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.FeatureSetDownlinkPerCC_Id.

Opaque FeatureSetDownlinkPerCC_Id__cond FeatureSetDownlinkPerCC_Id__Format.

Require Import NR.FeatureSetUplinkPerCC_Id.

Opaque FeatureSetUplinkPerCC_Id__cond FeatureSetUplinkPerCC_Id__Format.

Record ConfigRestrictInfoDAPS_v1640__Type : Set :=
  make__ConfigRestrictInfoDAPS_v1640__Type {
    ConfigRestrictInfoDAPS_v1640__sourceFeatureSetPerDownlinkCC_r16 : FeatureSetDownlinkPerCC_Id__Type ;
    ConfigRestrictInfoDAPS_v1640__sourceFeatureSetPerUplinkCC_r16 : FeatureSetUplinkPerCC_Id__Type ;
}.
Definition ConfigRestrictInfoDAPS_v1640__list := (
 Nor FeatureSetDownlinkPerCC_Id__Type FeatureSetDownlinkPerCC_Id__cond ::
 Nor FeatureSetUplinkPerCC_Id__Type FeatureSetUplinkPerCC_Id__cond ::
 nil).
Definition ConfigRestrictInfoDAPS_v1640__cond z := 
  FeatureSetDownlinkPerCC_Id__cond (ConfigRestrictInfoDAPS_v1640__sourceFeatureSetPerDownlinkCC_r16 z) /\
  FeatureSetUplinkPerCC_Id__cond (ConfigRestrictInfoDAPS_v1640__sourceFeatureSetPerUplinkCC_r16 z) /\
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

Definition ConfigRestrictInfoDAPS_v1640__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoDAPS_v1640__list.
Definition ConfigRestrictInfoDAPS_v1640__Format_list : ConfigRestrictInfoDAPS_v1640__Format_Type :=
  (FeatureSetDownlinkPerCC_Id__Format, (FeatureSetUplinkPerCC_Id__Format, unit_format)).
Definition ConfigRestrictInfoDAPS_v1640__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoDAPS_v1640__list ConfigRestrictInfoDAPS_v1640__Format_list.
Definition ConfigRestrictInfoDAPS_v1640__F1 z :=
  (ConfigRestrictInfoDAPS_v1640__sourceFeatureSetPerDownlinkCC_r16 z, (ConfigRestrictInfoDAPS_v1640__sourceFeatureSetPerUplinkCC_r16 z, tt)).
Definition ConfigRestrictInfoDAPS_v1640__F2 (y : seq_type ConfigRestrictInfoDAPS_v1640__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ConfigRestrictInfoDAPS_v1640__Type i0 i1
  end.
Lemma ConfigRestrictInfoDAPS_v1640__F1F2_cond (z : ConfigRestrictInfoDAPS_v1640__Type)
  : ConfigRestrictInfoDAPS_v1640__cond z ->
  (seq_cond ConfigRestrictInfoDAPS_v1640__list (ConfigRestrictInfoDAPS_v1640__F1 z)).
intro H. unfold ConfigRestrictInfoDAPS_v1640__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoDAPS_v1640__F1F2_cond2 (z : ConfigRestrictInfoDAPS_v1640__Type)
 : ConfigRestrictInfoDAPS_v1640__F2 (ConfigRestrictInfoDAPS_v1640__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoDAPS_v1640__F2F1_cond (y : seq_type ConfigRestrictInfoDAPS_v1640__list)
  : seq_cond ConfigRestrictInfoDAPS_v1640__list y ->
 (ConfigRestrictInfoDAPS_v1640__cond (ConfigRestrictInfoDAPS_v1640__F2 y)) /\  ConfigRestrictInfoDAPS_v1640__F1 (ConfigRestrictInfoDAPS_v1640__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoDAPS_v1640__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoDAPS_v1640__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoDAPS_v1640__Format : T_Format ConfigRestrictInfoDAPS_v1640__Type ConfigRestrictInfoDAPS_v1640__cond :=
        proj2_format  ConfigRestrictInfoDAPS_v1640__cond ConfigRestrictInfoDAPS_v1640__list__Format
    ConfigRestrictInfoDAPS_v1640__F1 ConfigRestrictInfoDAPS_v1640__F2 ConfigRestrictInfoDAPS_v1640__F1F2_cond  ConfigRestrictInfoDAPS_v1640__F1F2_cond2 ConfigRestrictInfoDAPS_v1640__F2F1_cond.
Opaque ConfigRestrictInfoDAPS_v1640__cond ConfigRestrictInfoDAPS_v1640__Format.

