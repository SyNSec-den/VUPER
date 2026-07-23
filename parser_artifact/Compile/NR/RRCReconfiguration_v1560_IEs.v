Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.MRDC_SecondaryCellGroupConfig.
Definition RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__Type := SetupRelease__Type MRDC_SecondaryCellGroupConfig__Type.
Definition RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__cond := SetupRelease__cond _ MRDC_SecondaryCellGroupConfig__cond.
Definition RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__Format : T_Format RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__Type RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__cond := SetupRelease__Format _ _ MRDC_SecondaryCellGroupConfig__Format.
Opaque RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__cond RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__Format.

Require Import NR.SK_Counter.

Opaque SK_Counter__cond SK_Counter__Format.

Require Import NR.RRCReconfiguration_v1610_IEs.

Opaque RRCReconfiguration_v1610_IEs__cond RRCReconfiguration_v1610_IEs__Format.

Record RRCReconfiguration_v1560_IEs__Type : Set :=
  make__RRCReconfiguration_v1560_IEs__Type {
    RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig : option RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__Type ;
    RRCReconfiguration_v1560_IEs__radioBearerConfig2 : option octet_string ;
    RRCReconfiguration_v1560_IEs__sk_Counter : option SK_Counter__Type ;
    RRCReconfiguration_v1560_IEs__nonCriticalExtension : option RRCReconfiguration_v1610_IEs__Type ;
}.
Definition RRCReconfiguration_v1560_IEs__list := (
 Opt RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__Type RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SK_Counter__Type SK_Counter__cond ::
 Opt RRCReconfiguration_v1610_IEs__Type RRCReconfiguration_v1610_IEs__cond ::
 nil).
Definition RRCReconfiguration_v1560_IEs__cond z := 
  opt_cond RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__cond (RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfiguration_v1560_IEs__radioBearerConfig2 z) /\
  opt_cond SK_Counter__cond (RRCReconfiguration_v1560_IEs__sk_Counter z) /\
  opt_cond RRCReconfiguration_v1610_IEs__cond (RRCReconfiguration_v1560_IEs__nonCriticalExtension z) /\
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
Opaque RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__cond RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__Format.


Definition RRCReconfiguration_v1560_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfiguration_v1560_IEs__list.
Definition RRCReconfiguration_v1560_IEs__Format_list : RRCReconfiguration_v1560_IEs__Format_Type :=
  (RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig__Format, (octet_string_nc__Format, (SK_Counter__Format, (RRCReconfiguration_v1610_IEs__Format, unit_format)))).
Definition RRCReconfiguration_v1560_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfiguration_v1560_IEs__list RRCReconfiguration_v1560_IEs__Format_list.
Definition RRCReconfiguration_v1560_IEs__F1 z :=
  (RRCReconfiguration_v1560_IEs__mrdc_SecondaryCellGroupConfig z, (RRCReconfiguration_v1560_IEs__radioBearerConfig2 z, (RRCReconfiguration_v1560_IEs__sk_Counter z, (RRCReconfiguration_v1560_IEs__nonCriticalExtension z, tt)))).
Definition RRCReconfiguration_v1560_IEs__F2 (y : seq_type RRCReconfiguration_v1560_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__RRCReconfiguration_v1560_IEs__Type i0 i1 i2 i3
  end.
Lemma RRCReconfiguration_v1560_IEs__F1F2_cond (z : RRCReconfiguration_v1560_IEs__Type)
  : RRCReconfiguration_v1560_IEs__cond z ->
  (seq_cond RRCReconfiguration_v1560_IEs__list (RRCReconfiguration_v1560_IEs__F1 z)).
intro H. unfold RRCReconfiguration_v1560_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfiguration_v1560_IEs__F1F2_cond2 (z : RRCReconfiguration_v1560_IEs__Type)
 : RRCReconfiguration_v1560_IEs__F2 (RRCReconfiguration_v1560_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfiguration_v1560_IEs__F2F1_cond (y : seq_type RRCReconfiguration_v1560_IEs__list)
  : seq_cond RRCReconfiguration_v1560_IEs__list y ->
 (RRCReconfiguration_v1560_IEs__cond (RRCReconfiguration_v1560_IEs__F2 y)) /\  RRCReconfiguration_v1560_IEs__F1 (RRCReconfiguration_v1560_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfiguration_v1560_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfiguration_v1560_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfiguration_v1560_IEs__Format : T_Format RRCReconfiguration_v1560_IEs__Type RRCReconfiguration_v1560_IEs__cond :=
        proj2_format  RRCReconfiguration_v1560_IEs__cond RRCReconfiguration_v1560_IEs__list__Format
    RRCReconfiguration_v1560_IEs__F1 RRCReconfiguration_v1560_IEs__F2 RRCReconfiguration_v1560_IEs__F1F2_cond  RRCReconfiguration_v1560_IEs__F1F2_cond2 RRCReconfiguration_v1560_IEs__F2F1_cond.
Opaque RRCReconfiguration_v1560_IEs__cond RRCReconfiguration_v1560_IEs__Format.

