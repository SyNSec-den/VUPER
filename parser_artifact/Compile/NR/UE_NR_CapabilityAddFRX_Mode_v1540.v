Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.IMS_ParametersFRX_Diff.

Opaque IMS_ParametersFRX_Diff__cond IMS_ParametersFRX_Diff__Format.

Record UE_NR_CapabilityAddFRX_Mode_v1540__Type : Set :=
  make__UE_NR_CapabilityAddFRX_Mode_v1540__Type {
    UE_NR_CapabilityAddFRX_Mode_v1540__ims_ParametersFRX_Diff : option IMS_ParametersFRX_Diff__Type ;
}.
Definition UE_NR_CapabilityAddFRX_Mode_v1540__list := (
 Opt IMS_ParametersFRX_Diff__Type IMS_ParametersFRX_Diff__cond ::
 nil).
Definition UE_NR_CapabilityAddFRX_Mode_v1540__cond z := 
  opt_cond IMS_ParametersFRX_Diff__cond (UE_NR_CapabilityAddFRX_Mode_v1540__ims_ParametersFRX_Diff z) /\
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

Definition UE_NR_CapabilityAddFRX_Mode_v1540__Format_Type := Eval cbn in seq_format_prod UE_NR_CapabilityAddFRX_Mode_v1540__list.
Definition UE_NR_CapabilityAddFRX_Mode_v1540__Format_list : UE_NR_CapabilityAddFRX_Mode_v1540__Format_Type :=
  (IMS_ParametersFRX_Diff__Format, unit_format).
Definition UE_NR_CapabilityAddFRX_Mode_v1540__list__Format := (*Eval compute in *) seq_format UE_NR_CapabilityAddFRX_Mode_v1540__list UE_NR_CapabilityAddFRX_Mode_v1540__Format_list.
Definition UE_NR_CapabilityAddFRX_Mode_v1540__F1 z :=
  (UE_NR_CapabilityAddFRX_Mode_v1540__ims_ParametersFRX_Diff z, tt).
Definition UE_NR_CapabilityAddFRX_Mode_v1540__F2 (y : seq_type UE_NR_CapabilityAddFRX_Mode_v1540__list) :=
  match y with
  | (i0, _)=>
    make__UE_NR_CapabilityAddFRX_Mode_v1540__Type i0
  end.
Lemma UE_NR_CapabilityAddFRX_Mode_v1540__F1F2_cond (z : UE_NR_CapabilityAddFRX_Mode_v1540__Type)
  : UE_NR_CapabilityAddFRX_Mode_v1540__cond z ->
  (seq_cond UE_NR_CapabilityAddFRX_Mode_v1540__list (UE_NR_CapabilityAddFRX_Mode_v1540__F1 z)).
intro H. unfold UE_NR_CapabilityAddFRX_Mode_v1540__cond in H. simpl. auto. Qed.
Lemma UE_NR_CapabilityAddFRX_Mode_v1540__F1F2_cond2 (z : UE_NR_CapabilityAddFRX_Mode_v1540__Type)
 : UE_NR_CapabilityAddFRX_Mode_v1540__F2 (UE_NR_CapabilityAddFRX_Mode_v1540__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_NR_CapabilityAddFRX_Mode_v1540__F2F1_cond (y : seq_type UE_NR_CapabilityAddFRX_Mode_v1540__list)
  : seq_cond UE_NR_CapabilityAddFRX_Mode_v1540__list y ->
 (UE_NR_CapabilityAddFRX_Mode_v1540__cond (UE_NR_CapabilityAddFRX_Mode_v1540__F2 y)) /\  UE_NR_CapabilityAddFRX_Mode_v1540__F1 (UE_NR_CapabilityAddFRX_Mode_v1540__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_NR_CapabilityAddFRX_Mode_v1540__cond. simpl in *. auto.
 - simpl. unfold UE_NR_CapabilityAddFRX_Mode_v1540__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_NR_CapabilityAddFRX_Mode_v1540__Format : T_Format UE_NR_CapabilityAddFRX_Mode_v1540__Type UE_NR_CapabilityAddFRX_Mode_v1540__cond :=
        proj2_format  UE_NR_CapabilityAddFRX_Mode_v1540__cond UE_NR_CapabilityAddFRX_Mode_v1540__list__Format
    UE_NR_CapabilityAddFRX_Mode_v1540__F1 UE_NR_CapabilityAddFRX_Mode_v1540__F2 UE_NR_CapabilityAddFRX_Mode_v1540__F1F2_cond  UE_NR_CapabilityAddFRX_Mode_v1540__F1F2_cond2 UE_NR_CapabilityAddFRX_Mode_v1540__F2F1_cond.
Opaque UE_NR_CapabilityAddFRX_Mode_v1540__cond UE_NR_CapabilityAddFRX_Mode_v1540__Format.

