Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_ConfigMobility.

Opaque SSB_ConfigMobility__cond SSB_ConfigMobility__Format.

Require Import NR.SetupRelease.
Require Import NR.CSI_RS_ResourceConfigMobility.
Definition ReferenceSignalConfig__csi_rs_ResourceConfigMobility__Type := SetupRelease__Type CSI_RS_ResourceConfigMobility__Type.
Definition ReferenceSignalConfig__csi_rs_ResourceConfigMobility__cond := SetupRelease__cond _ CSI_RS_ResourceConfigMobility__cond.
Definition ReferenceSignalConfig__csi_rs_ResourceConfigMobility__Format : T_Format ReferenceSignalConfig__csi_rs_ResourceConfigMobility__Type ReferenceSignalConfig__csi_rs_ResourceConfigMobility__cond := SetupRelease__Format _ _ CSI_RS_ResourceConfigMobility__Format.
Opaque ReferenceSignalConfig__csi_rs_ResourceConfigMobility__cond ReferenceSignalConfig__csi_rs_ResourceConfigMobility__Format.

Record ReferenceSignalConfig__Type : Set :=
  make__ReferenceSignalConfig__Type {
    ReferenceSignalConfig__ssb_ConfigMobility : option SSB_ConfigMobility__Type ;
    ReferenceSignalConfig__csi_rs_ResourceConfigMobility : option ReferenceSignalConfig__csi_rs_ResourceConfigMobility__Type ;
}.
Definition ReferenceSignalConfig__list := (
 Opt SSB_ConfigMobility__Type SSB_ConfigMobility__cond ::
 Opt ReferenceSignalConfig__csi_rs_ResourceConfigMobility__Type ReferenceSignalConfig__csi_rs_ResourceConfigMobility__cond ::
 nil).
Definition ReferenceSignalConfig__cond z := 
  opt_cond SSB_ConfigMobility__cond (ReferenceSignalConfig__ssb_ConfigMobility z) /\
  opt_cond ReferenceSignalConfig__csi_rs_ResourceConfigMobility__cond (ReferenceSignalConfig__csi_rs_ResourceConfigMobility z) /\
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
Opaque ReferenceSignalConfig__csi_rs_ResourceConfigMobility__cond ReferenceSignalConfig__csi_rs_ResourceConfigMobility__Format.


Definition ReferenceSignalConfig__Format_Type := Eval cbn in seq_format_prod ReferenceSignalConfig__list.
Definition ReferenceSignalConfig__Format_list : ReferenceSignalConfig__Format_Type :=
  (SSB_ConfigMobility__Format, (ReferenceSignalConfig__csi_rs_ResourceConfigMobility__Format, unit_format)).
Definition ReferenceSignalConfig__list__Format := (*Eval compute in *) seq_format ReferenceSignalConfig__list ReferenceSignalConfig__Format_list.
Definition ReferenceSignalConfig__F1 z :=
  (ReferenceSignalConfig__ssb_ConfigMobility z, (ReferenceSignalConfig__csi_rs_ResourceConfigMobility z, tt)).
Definition ReferenceSignalConfig__F2 (y : seq_type ReferenceSignalConfig__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ReferenceSignalConfig__Type i0 i1
  end.
Lemma ReferenceSignalConfig__F1F2_cond (z : ReferenceSignalConfig__Type)
  : ReferenceSignalConfig__cond z ->
  (seq_cond ReferenceSignalConfig__list (ReferenceSignalConfig__F1 z)).
intro H. unfold ReferenceSignalConfig__cond in H. simpl. auto. Qed.
Lemma ReferenceSignalConfig__F1F2_cond2 (z : ReferenceSignalConfig__Type)
 : ReferenceSignalConfig__F2 (ReferenceSignalConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReferenceSignalConfig__F2F1_cond (y : seq_type ReferenceSignalConfig__list)
  : seq_cond ReferenceSignalConfig__list y ->
 (ReferenceSignalConfig__cond (ReferenceSignalConfig__F2 y)) /\  ReferenceSignalConfig__F1 (ReferenceSignalConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReferenceSignalConfig__cond. simpl in *. auto.
 - simpl. unfold ReferenceSignalConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReferenceSignalConfig__Format : T_Format ReferenceSignalConfig__Type ReferenceSignalConfig__cond :=
        proj2_format  ReferenceSignalConfig__cond ReferenceSignalConfig__list__Format
    ReferenceSignalConfig__F1 ReferenceSignalConfig__F2 ReferenceSignalConfig__F1F2_cond  ReferenceSignalConfig__F1F2_cond2 ReferenceSignalConfig__F2F1_cond.
Opaque ReferenceSignalConfig__cond ReferenceSignalConfig__Format.

