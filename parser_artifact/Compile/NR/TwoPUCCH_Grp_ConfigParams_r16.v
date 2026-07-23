Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUCCH_Grp_CarrierTypes_r16.

Opaque PUCCH_Grp_CarrierTypes_r16__cond PUCCH_Grp_CarrierTypes_r16__Format.

Require Import NR.PUCCH_Grp_CarrierTypes_r16.

Opaque PUCCH_Grp_CarrierTypes_r16__cond PUCCH_Grp_CarrierTypes_r16__Format.

Record TwoPUCCH_Grp_ConfigParams_r16__Type : Set :=
  make__TwoPUCCH_Grp_ConfigParams_r16__Type {
    TwoPUCCH_Grp_ConfigParams_r16__pucch_GroupMapping_r16 : PUCCH_Grp_CarrierTypes_r16__Type ;
    TwoPUCCH_Grp_ConfigParams_r16__pucch_TX_r16 : PUCCH_Grp_CarrierTypes_r16__Type ;
}.
Definition TwoPUCCH_Grp_ConfigParams_r16__list := (
 Nor PUCCH_Grp_CarrierTypes_r16__Type PUCCH_Grp_CarrierTypes_r16__cond ::
 Nor PUCCH_Grp_CarrierTypes_r16__Type PUCCH_Grp_CarrierTypes_r16__cond ::
 nil).
Definition TwoPUCCH_Grp_ConfigParams_r16__cond z := 
  PUCCH_Grp_CarrierTypes_r16__cond (TwoPUCCH_Grp_ConfigParams_r16__pucch_GroupMapping_r16 z) /\
  PUCCH_Grp_CarrierTypes_r16__cond (TwoPUCCH_Grp_ConfigParams_r16__pucch_TX_r16 z) /\
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

Definition TwoPUCCH_Grp_ConfigParams_r16__Format_Type := Eval cbn in seq_format_prod TwoPUCCH_Grp_ConfigParams_r16__list.
Definition TwoPUCCH_Grp_ConfigParams_r16__Format_list : TwoPUCCH_Grp_ConfigParams_r16__Format_Type :=
  (PUCCH_Grp_CarrierTypes_r16__Format, (PUCCH_Grp_CarrierTypes_r16__Format, unit_format)).
Definition TwoPUCCH_Grp_ConfigParams_r16__list__Format := (*Eval compute in *) seq_format TwoPUCCH_Grp_ConfigParams_r16__list TwoPUCCH_Grp_ConfigParams_r16__Format_list.
Definition TwoPUCCH_Grp_ConfigParams_r16__F1 z :=
  (TwoPUCCH_Grp_ConfigParams_r16__pucch_GroupMapping_r16 z, (TwoPUCCH_Grp_ConfigParams_r16__pucch_TX_r16 z, tt)).
Definition TwoPUCCH_Grp_ConfigParams_r16__F2 (y : seq_type TwoPUCCH_Grp_ConfigParams_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__TwoPUCCH_Grp_ConfigParams_r16__Type i0 i1
  end.
Lemma TwoPUCCH_Grp_ConfigParams_r16__F1F2_cond (z : TwoPUCCH_Grp_ConfigParams_r16__Type)
  : TwoPUCCH_Grp_ConfigParams_r16__cond z ->
  (seq_cond TwoPUCCH_Grp_ConfigParams_r16__list (TwoPUCCH_Grp_ConfigParams_r16__F1 z)).
intro H. unfold TwoPUCCH_Grp_ConfigParams_r16__cond in H. simpl. auto. Qed.
Lemma TwoPUCCH_Grp_ConfigParams_r16__F1F2_cond2 (z : TwoPUCCH_Grp_ConfigParams_r16__Type)
 : TwoPUCCH_Grp_ConfigParams_r16__F2 (TwoPUCCH_Grp_ConfigParams_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma TwoPUCCH_Grp_ConfigParams_r16__F2F1_cond (y : seq_type TwoPUCCH_Grp_ConfigParams_r16__list)
  : seq_cond TwoPUCCH_Grp_ConfigParams_r16__list y ->
 (TwoPUCCH_Grp_ConfigParams_r16__cond (TwoPUCCH_Grp_ConfigParams_r16__F2 y)) /\  TwoPUCCH_Grp_ConfigParams_r16__F1 (TwoPUCCH_Grp_ConfigParams_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold TwoPUCCH_Grp_ConfigParams_r16__cond. simpl in *. auto.
 - simpl. unfold TwoPUCCH_Grp_ConfigParams_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition TwoPUCCH_Grp_ConfigParams_r16__Format : T_Format TwoPUCCH_Grp_ConfigParams_r16__Type TwoPUCCH_Grp_ConfigParams_r16__cond :=
        proj2_format  TwoPUCCH_Grp_ConfigParams_r16__cond TwoPUCCH_Grp_ConfigParams_r16__list__Format
    TwoPUCCH_Grp_ConfigParams_r16__F1 TwoPUCCH_Grp_ConfigParams_r16__F2 TwoPUCCH_Grp_ConfigParams_r16__F1F2_cond  TwoPUCCH_Grp_ConfigParams_r16__F1F2_cond2 TwoPUCCH_Grp_ConfigParams_r16__F2F1_cond.
Opaque TwoPUCCH_Grp_ConfigParams_r16__cond TwoPUCCH_Grp_ConfigParams_r16__Format.

