Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PowSav_ParametersFRX_Diff_r16.

Opaque PowSav_ParametersFRX_Diff_r16__cond PowSav_ParametersFRX_Diff_r16__Format.

Require Import NR.MAC_ParametersFRX_Diff_r16.

Opaque MAC_ParametersFRX_Diff_r16__cond MAC_ParametersFRX_Diff_r16__Format.

Record UE_NR_CapabilityAddFRX_Mode_v1610__Type : Set :=
  make__UE_NR_CapabilityAddFRX_Mode_v1610__Type {
    UE_NR_CapabilityAddFRX_Mode_v1610__powSav_ParametersFRX_Diff_r16 : option PowSav_ParametersFRX_Diff_r16__Type ;
    UE_NR_CapabilityAddFRX_Mode_v1610__mac_ParametersFRX_Diff_r16 : option MAC_ParametersFRX_Diff_r16__Type ;
}.
Definition UE_NR_CapabilityAddFRX_Mode_v1610__list := (
 Opt PowSav_ParametersFRX_Diff_r16__Type PowSav_ParametersFRX_Diff_r16__cond ::
 Opt MAC_ParametersFRX_Diff_r16__Type MAC_ParametersFRX_Diff_r16__cond ::
 nil).
Definition UE_NR_CapabilityAddFRX_Mode_v1610__cond z := 
  opt_cond PowSav_ParametersFRX_Diff_r16__cond (UE_NR_CapabilityAddFRX_Mode_v1610__powSav_ParametersFRX_Diff_r16 z) /\
  opt_cond MAC_ParametersFRX_Diff_r16__cond (UE_NR_CapabilityAddFRX_Mode_v1610__mac_ParametersFRX_Diff_r16 z) /\
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

Definition UE_NR_CapabilityAddFRX_Mode_v1610__Format_Type := Eval cbn in seq_format_prod UE_NR_CapabilityAddFRX_Mode_v1610__list.
Definition UE_NR_CapabilityAddFRX_Mode_v1610__Format_list : UE_NR_CapabilityAddFRX_Mode_v1610__Format_Type :=
  (PowSav_ParametersFRX_Diff_r16__Format, (MAC_ParametersFRX_Diff_r16__Format, unit_format)).
Definition UE_NR_CapabilityAddFRX_Mode_v1610__list__Format := (*Eval compute in *) seq_format UE_NR_CapabilityAddFRX_Mode_v1610__list UE_NR_CapabilityAddFRX_Mode_v1610__Format_list.
Definition UE_NR_CapabilityAddFRX_Mode_v1610__F1 z :=
  (UE_NR_CapabilityAddFRX_Mode_v1610__powSav_ParametersFRX_Diff_r16 z, (UE_NR_CapabilityAddFRX_Mode_v1610__mac_ParametersFRX_Diff_r16 z, tt)).
Definition UE_NR_CapabilityAddFRX_Mode_v1610__F2 (y : seq_type UE_NR_CapabilityAddFRX_Mode_v1610__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UE_NR_CapabilityAddFRX_Mode_v1610__Type i0 i1
  end.
Lemma UE_NR_CapabilityAddFRX_Mode_v1610__F1F2_cond (z : UE_NR_CapabilityAddFRX_Mode_v1610__Type)
  : UE_NR_CapabilityAddFRX_Mode_v1610__cond z ->
  (seq_cond UE_NR_CapabilityAddFRX_Mode_v1610__list (UE_NR_CapabilityAddFRX_Mode_v1610__F1 z)).
intro H. unfold UE_NR_CapabilityAddFRX_Mode_v1610__cond in H. simpl. auto. Qed.
Lemma UE_NR_CapabilityAddFRX_Mode_v1610__F1F2_cond2 (z : UE_NR_CapabilityAddFRX_Mode_v1610__Type)
 : UE_NR_CapabilityAddFRX_Mode_v1610__F2 (UE_NR_CapabilityAddFRX_Mode_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_NR_CapabilityAddFRX_Mode_v1610__F2F1_cond (y : seq_type UE_NR_CapabilityAddFRX_Mode_v1610__list)
  : seq_cond UE_NR_CapabilityAddFRX_Mode_v1610__list y ->
 (UE_NR_CapabilityAddFRX_Mode_v1610__cond (UE_NR_CapabilityAddFRX_Mode_v1610__F2 y)) /\  UE_NR_CapabilityAddFRX_Mode_v1610__F1 (UE_NR_CapabilityAddFRX_Mode_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_NR_CapabilityAddFRX_Mode_v1610__cond. simpl in *. auto.
 - simpl. unfold UE_NR_CapabilityAddFRX_Mode_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_NR_CapabilityAddFRX_Mode_v1610__Format : T_Format UE_NR_CapabilityAddFRX_Mode_v1610__Type UE_NR_CapabilityAddFRX_Mode_v1610__cond :=
        proj2_format  UE_NR_CapabilityAddFRX_Mode_v1610__cond UE_NR_CapabilityAddFRX_Mode_v1610__list__Format
    UE_NR_CapabilityAddFRX_Mode_v1610__F1 UE_NR_CapabilityAddFRX_Mode_v1610__F2 UE_NR_CapabilityAddFRX_Mode_v1610__F1F2_cond  UE_NR_CapabilityAddFRX_Mode_v1610__F1F2_cond2 UE_NR_CapabilityAddFRX_Mode_v1610__F2F1_cond.
Opaque UE_NR_CapabilityAddFRX_Mode_v1610__cond UE_NR_CapabilityAddFRX_Mode_v1610__Format.

