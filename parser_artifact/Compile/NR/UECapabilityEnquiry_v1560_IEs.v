Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UE_CapabilityRequestFilterCommon.

Opaque UE_CapabilityRequestFilterCommon__cond UE_CapabilityRequestFilterCommon__Format.

Require Import NR.UECapabilityEnquiry_v1610_IEs.

Opaque UECapabilityEnquiry_v1610_IEs__cond UECapabilityEnquiry_v1610_IEs__Format.

Record UECapabilityEnquiry_v1560_IEs__Type : Set :=
  make__UECapabilityEnquiry_v1560_IEs__Type {
    UECapabilityEnquiry_v1560_IEs__capabilityRequestFilterCommon : option UE_CapabilityRequestFilterCommon__Type ;
    UECapabilityEnquiry_v1560_IEs__nonCriticalExtension : option UECapabilityEnquiry_v1610_IEs__Type ;
}.
Definition UECapabilityEnquiry_v1560_IEs__list := (
 Opt UE_CapabilityRequestFilterCommon__Type UE_CapabilityRequestFilterCommon__cond ::
 Opt UECapabilityEnquiry_v1610_IEs__Type UECapabilityEnquiry_v1610_IEs__cond ::
 nil).
Definition UECapabilityEnquiry_v1560_IEs__cond z := 
  opt_cond UE_CapabilityRequestFilterCommon__cond (UECapabilityEnquiry_v1560_IEs__capabilityRequestFilterCommon z) /\
  opt_cond UECapabilityEnquiry_v1610_IEs__cond (UECapabilityEnquiry_v1560_IEs__nonCriticalExtension z) /\
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

Definition UECapabilityEnquiry_v1560_IEs__Format_Type := Eval cbn in seq_format_prod UECapabilityEnquiry_v1560_IEs__list.
Definition UECapabilityEnquiry_v1560_IEs__Format_list : UECapabilityEnquiry_v1560_IEs__Format_Type :=
  (UE_CapabilityRequestFilterCommon__Format, (UECapabilityEnquiry_v1610_IEs__Format, unit_format)).
Definition UECapabilityEnquiry_v1560_IEs__list__Format := (*Eval compute in *) seq_format UECapabilityEnquiry_v1560_IEs__list UECapabilityEnquiry_v1560_IEs__Format_list.
Definition UECapabilityEnquiry_v1560_IEs__F1 z :=
  (UECapabilityEnquiry_v1560_IEs__capabilityRequestFilterCommon z, (UECapabilityEnquiry_v1560_IEs__nonCriticalExtension z, tt)).
Definition UECapabilityEnquiry_v1560_IEs__F2 (y : seq_type UECapabilityEnquiry_v1560_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UECapabilityEnquiry_v1560_IEs__Type i0 i1
  end.
Lemma UECapabilityEnquiry_v1560_IEs__F1F2_cond (z : UECapabilityEnquiry_v1560_IEs__Type)
  : UECapabilityEnquiry_v1560_IEs__cond z ->
  (seq_cond UECapabilityEnquiry_v1560_IEs__list (UECapabilityEnquiry_v1560_IEs__F1 z)).
intro H. unfold UECapabilityEnquiry_v1560_IEs__cond in H. simpl. auto. Qed.
Lemma UECapabilityEnquiry_v1560_IEs__F1F2_cond2 (z : UECapabilityEnquiry_v1560_IEs__Type)
 : UECapabilityEnquiry_v1560_IEs__F2 (UECapabilityEnquiry_v1560_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UECapabilityEnquiry_v1560_IEs__F2F1_cond (y : seq_type UECapabilityEnquiry_v1560_IEs__list)
  : seq_cond UECapabilityEnquiry_v1560_IEs__list y ->
 (UECapabilityEnquiry_v1560_IEs__cond (UECapabilityEnquiry_v1560_IEs__F2 y)) /\  UECapabilityEnquiry_v1560_IEs__F1 (UECapabilityEnquiry_v1560_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UECapabilityEnquiry_v1560_IEs__cond. simpl in *. auto.
 - simpl. unfold UECapabilityEnquiry_v1560_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UECapabilityEnquiry_v1560_IEs__Format : T_Format UECapabilityEnquiry_v1560_IEs__Type UECapabilityEnquiry_v1560_IEs__cond :=
        proj2_format  UECapabilityEnquiry_v1560_IEs__cond UECapabilityEnquiry_v1560_IEs__list__Format
    UECapabilityEnquiry_v1560_IEs__F1 UECapabilityEnquiry_v1560_IEs__F2 UECapabilityEnquiry_v1560_IEs__F1F2_cond  UECapabilityEnquiry_v1560_IEs__F1F2_cond2 UECapabilityEnquiry_v1560_IEs__F2F1_cond.
Opaque UECapabilityEnquiry_v1560_IEs__cond UECapabilityEnquiry_v1560_IEs__Format.

