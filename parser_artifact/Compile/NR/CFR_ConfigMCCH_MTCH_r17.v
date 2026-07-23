Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.LocationAndBandwidthBroadcast_r17.

Opaque LocationAndBandwidthBroadcast_r17__cond LocationAndBandwidthBroadcast_r17__Format.

Require Import NR.PDSCH_ConfigBroadcast_r17.

Opaque PDSCH_ConfigBroadcast_r17__cond PDSCH_ConfigBroadcast_r17__Format.

Require Import NR.ControlResourceSet.

Opaque ControlResourceSet__cond ControlResourceSet__Format.

Record CFR_ConfigMCCH_MTCH_r17__Type : Set :=
  make__CFR_ConfigMCCH_MTCH_r17__Type {
    CFR_ConfigMCCH_MTCH_r17__locationAndBandwidthBroadcast_r17 : option LocationAndBandwidthBroadcast_r17__Type ;
    CFR_ConfigMCCH_MTCH_r17__pdsch_ConfigMCCH_r17 : option PDSCH_ConfigBroadcast_r17__Type ;
    CFR_ConfigMCCH_MTCH_r17__commonControlResourceSetExt_r17 : option ControlResourceSet__Type ;
}.
Definition CFR_ConfigMCCH_MTCH_r17__list := (
 Opt LocationAndBandwidthBroadcast_r17__Type LocationAndBandwidthBroadcast_r17__cond ::
 Opt PDSCH_ConfigBroadcast_r17__Type PDSCH_ConfigBroadcast_r17__cond ::
 Opt ControlResourceSet__Type ControlResourceSet__cond ::
 nil).
Definition CFR_ConfigMCCH_MTCH_r17__cond z := 
  opt_cond LocationAndBandwidthBroadcast_r17__cond (CFR_ConfigMCCH_MTCH_r17__locationAndBandwidthBroadcast_r17 z) /\
  opt_cond PDSCH_ConfigBroadcast_r17__cond (CFR_ConfigMCCH_MTCH_r17__pdsch_ConfigMCCH_r17 z) /\
  opt_cond ControlResourceSet__cond (CFR_ConfigMCCH_MTCH_r17__commonControlResourceSetExt_r17 z) /\
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

Definition CFR_ConfigMCCH_MTCH_r17__Format_Type := Eval cbn in seq_format_prod CFR_ConfigMCCH_MTCH_r17__list.
Definition CFR_ConfigMCCH_MTCH_r17__Format_list : CFR_ConfigMCCH_MTCH_r17__Format_Type :=
  (LocationAndBandwidthBroadcast_r17__Format, (PDSCH_ConfigBroadcast_r17__Format, (ControlResourceSet__Format, unit_format))).
Definition CFR_ConfigMCCH_MTCH_r17__list__Format := (*Eval compute in *) seq_format CFR_ConfigMCCH_MTCH_r17__list CFR_ConfigMCCH_MTCH_r17__Format_list.
Definition CFR_ConfigMCCH_MTCH_r17__F1 z :=
  (CFR_ConfigMCCH_MTCH_r17__locationAndBandwidthBroadcast_r17 z, (CFR_ConfigMCCH_MTCH_r17__pdsch_ConfigMCCH_r17 z, (CFR_ConfigMCCH_MTCH_r17__commonControlResourceSetExt_r17 z, tt))).
Definition CFR_ConfigMCCH_MTCH_r17__F2 (y : seq_type CFR_ConfigMCCH_MTCH_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CFR_ConfigMCCH_MTCH_r17__Type i0 i1 i2
  end.
Lemma CFR_ConfigMCCH_MTCH_r17__F1F2_cond (z : CFR_ConfigMCCH_MTCH_r17__Type)
  : CFR_ConfigMCCH_MTCH_r17__cond z ->
  (seq_cond CFR_ConfigMCCH_MTCH_r17__list (CFR_ConfigMCCH_MTCH_r17__F1 z)).
intro H. unfold CFR_ConfigMCCH_MTCH_r17__cond in H. simpl. auto. Qed.
Lemma CFR_ConfigMCCH_MTCH_r17__F1F2_cond2 (z : CFR_ConfigMCCH_MTCH_r17__Type)
 : CFR_ConfigMCCH_MTCH_r17__F2 (CFR_ConfigMCCH_MTCH_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFR_ConfigMCCH_MTCH_r17__F2F1_cond (y : seq_type CFR_ConfigMCCH_MTCH_r17__list)
  : seq_cond CFR_ConfigMCCH_MTCH_r17__list y ->
 (CFR_ConfigMCCH_MTCH_r17__cond (CFR_ConfigMCCH_MTCH_r17__F2 y)) /\  CFR_ConfigMCCH_MTCH_r17__F1 (CFR_ConfigMCCH_MTCH_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFR_ConfigMCCH_MTCH_r17__cond. simpl in *. auto.
 - simpl. unfold CFR_ConfigMCCH_MTCH_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFR_ConfigMCCH_MTCH_r17__Format : T_Format CFR_ConfigMCCH_MTCH_r17__Type CFR_ConfigMCCH_MTCH_r17__cond :=
        proj2_format  CFR_ConfigMCCH_MTCH_r17__cond CFR_ConfigMCCH_MTCH_r17__list__Format
    CFR_ConfigMCCH_MTCH_r17__F1 CFR_ConfigMCCH_MTCH_r17__F2 CFR_ConfigMCCH_MTCH_r17__F1F2_cond  CFR_ConfigMCCH_MTCH_r17__F1F2_cond2 CFR_ConfigMCCH_MTCH_r17__F2F1_cond.
Opaque CFR_ConfigMCCH_MTCH_r17__cond CFR_ConfigMCCH_MTCH_r17__Format.

